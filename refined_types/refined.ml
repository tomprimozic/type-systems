open Expr

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)
module Env = Infer.Env


exception Error of string
let error msg = raise (Error msg)


module Z3 = struct
	let info = ref None
	let log = ref ""

	let is_started () = None != !info

	let stop () =
		match !info with
			| None -> error "Z3 not running"
			| Some(pid, c_in, c_out) ->
				if Unix.getpid () = pid then begin
					let process_status = Unix.close_process (c_in, c_out) in
					begin match process_status with
						| Unix.WEXITED 0 -> ()
						| Unix.WEXITED exit_code -> Printf.printf "Z3 exited with exit code %i\n" exit_code
						| Unix.WSIGNALED signal -> Printf.printf "Z3 was killed by a signal %i\n" signal
						| Unix.WSTOPPED signal -> Printf.printf "Z3 was stopped by a signal %i\n" signal
					end ;
					if process_status <> Unix.WEXITED 1 then begin
						print_endline "\n\nZ3 LOG\n" ;
						print_endline !log
					end
				end ;
				info := None

	let start () =
		if not (is_started ()) then begin
			let c_in, c_out = Unix.open_process "z3 -smt2 -in" in
			info := Some (Unix.getpid (), c_in, c_out) ;
			at_exit stop
		end

	let get_out_channel () =
		match !info with
			| None -> error "Z3 not running"
			| Some (_, _, c_out) -> c_out

	let get_in_channel () =
		match !info with
			| None -> error "Z3 not running"
			| Some (_, c_in, _) -> c_in

	let read () =
		let c_in = get_in_channel () in
		input_line c_in

	let write str =
		let c_out = get_out_channel () in
		output_string c_out str ;
		output_char c_out '\n' ;
		flush c_out ;
		log := !log ^ str ^ "\n"

	let push () = write "(push)"
	let pop () = write "(pop)\n"
end


let builtins =
	List.fold_left
		(fun names (name, ty_str) -> StringSet.add name names)
		StringSet.empty Core.builtins

let uninterpreted =
	List.fold_left
		(fun names (name, ty_str) ->
			begin match Env.lookup Core.env name with
				| TArrow _ -> ()
				| _ -> error ("uninterpreted symbol " ^ name ^ " is not a function")
			end ;
			StringSet.add name names)
		StringSet.empty Core.uninterpreted

let primitives =
	List.fold_left
		(fun names (name, ty_str) -> StringSet.add name names)
		StringSet.empty Core.primitives

(*
and t_expr_shape =
	| EVar of name
	| EBool of bool
	| EInt of int
	| ECall of t_expr * t_expr list
	| EFun of t_param list * (t_ty * (name * t_expr) option) option * t_expr
	| ELet of name * t_expr * t_expr
	| EIf of t_expr * t_expr * t_expr
	| ECast of t_expr * t_ty * t_expr option
*)

let check_expr_ty expr =
	match get_real_ty expr.ty with
		| TConst "int" | TConst "bool" -> ()
		| _ -> error ("only int or bool, not " ^ string_of_plain_ty expr.ty)

let translate_ty ty =
	match get_real_ty ty with
		| TConst "int" -> "Int"
		| TConst "bool" -> "Bool"
		| _ -> error ("can translate only int or bool, not " ^ string_of_plain_ty ty)

let translate_builtin fn args =
	let args_string = String.concat " " args in
	match fn with
		| "unary-" -> "(- " ^ args_string ^ ")"
		| "!=" -> "(not (= " ^ args_string ^ "))"
		| "==" -> "(= " ^ args_string ^ ")"
		| _ -> "(" ^ fn ^ " " ^ args_string ^ ")"

let rec translate expr =
	check_expr_ty expr ;
	match expr.shape with
	| EVar name -> name
	| EInt i -> string_of_int i
	| EBool b -> string_of_bool b
	| ECall({shape = EVar fn_name; ty = _}, arg_list) ->
			if not (StringSet.mem fn_name builtins) then error "translate NI only builtins" else
			if fn_name == "/" then error "translate NI /" else 
			translate_builtin fn_name (List.map translate arg_list)
	| _ -> error "translate NI check_contract"

let check_contract contract =
	Z3.push () ;
	Z3.write ("(assert (not " ^ translate contract ^ "))") ;
	Z3.write "(check-sat)" ;
	Z3.pop () ;
	let answer = Z3.read () in
	if answer <> "unsat" then error ("Z3 returned " ^ answer)

let rec check_expr expr = match expr.shape with
	| EVar name -> name
	| EBool b -> string_of_bool b
	| EInt i -> string_of_int i
	| ECast(expr, ty, Some refined_expr) ->
			let ty = get_real_ty ty in
			if (ty <> t_bool) && (ty <> t_int) then error ("not implemented - check_expr cast " ^ string_of_plain_ty ty) else
			check_contract refined_expr ;
			check_expr expr
	| ELet(var_name, value_expr, body_expr) ->
			let translated_ty = translate_ty value_expr.ty in
			Z3.write ("(declare-const " ^ var_name ^ " " ^ translated_ty ^ ")") ;
			let translated_value = check_expr value_expr in
			Z3.write ("(assert (= " ^ var_name ^ " " ^ translated_value ^ "))") ;
			check_expr body_expr
	| _ -> error "not implemented - check_expr"
	

let prove expr =
	Z3.start () ;
	ignore (check_expr expr)
