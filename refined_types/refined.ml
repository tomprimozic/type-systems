open Expr
open Printing
open Smt

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)


exception Error of string
let error msg = raise (Error msg)


type result = Term | Formula


module LocalEnv = struct
	type env = string StringMap.t

	let empty : env = StringMap.empty
	let extend name ty env =
		if StringMap.mem name env then error ("duplicate variable name \"" ^ name ^ "\"") else
		StringMap.add name ty env
	let lookup name env =
		try
			StringMap.find name env
		with Not_found ->
			name
end

module FnEnv = struct
	type env = (LocalEnv.env * t_ty) StringMap.t

	let empty : env = StringMap.empty
	let extend name local_env_and_ty env =
		if StringMap.mem name env then error ("duplicate variable name \"" ^ name ^ "\"") else
		StringMap.add name local_env_and_ty env
	let lookup name env = StringMap.find name env
end




let builtins =
	List.fold_left
		(fun names (name, ty_str) ->
			if not (is_function_ty (Infer.Env.lookup name Core.env)) then
				error ("builtin symbol " ^ name ^ " must be a function")
			else
				StringSet.add name names)
		StringSet.empty Core.builtins

let uninterpreted =
	List.fold_left
		(fun names (name, ty_str) ->
			if not (is_function_ty (Infer.Env.lookup name Core.env)) then
				error ("uninterpreted symbol " ^ name ^ " must be a function")
			else
				StringSet.add name names)
		StringSet.empty Core.uninterpreted

let primitives =
	List.fold_left
		(fun names (name, ty_str) -> StringSet.add name names)
		StringSet.empty Core.primitives





let translate_bool = string_of_bool

let translate_int = string_of_int

let translate_ty ty =
	match real_ty ty with
		| TConst "int" -> "Int"
		| TConst "bool" -> "Bool"
		| TConst _ | TApp _ | TVar _ -> "Other"
		| TArrow _ -> error "cannot translate function types"

let translate_builtin_and_uninterpreted fn_name translated_arg_list =
	assert (StringSet.mem fn_name builtins || StringSet.mem fn_name uninterpreted) ;
	match (fn_name, translated_arg_list) with
		| ("<", [a; b]) -> "(<= " ^ a ^ " (- " ^ b ^ " 1))"
		| (">", [a; b]) -> "(>= (- " ^ a ^ " 1) " ^ b ^ ")"
		| _ ->
	let args = String.concat " " translated_arg_list in
	match fn_name with
		| "unary-" -> "(- " ^ args ^ ")"
		| "%" -> "(mod " ^ args ^ ")"
		| "!=" -> "(not (= " ^ args ^ "))"
		| "==" -> "(= " ^ args ^ ")"
		| _ -> "(" ^ fn_name ^ " " ^ args ^ ")"




let declare_var name ty =
	let translated_ty = translate_ty ty in
	Smt.write ("(declare-const " ^ name ^ " " ^ translated_ty ^ ")")


let var_name_map = Hashtbl.create 5
let declare_new_var ty =
	let var_name = match real_ty ty with
		| TConst name | TApp(name, _) -> String.make 1 (String.get name 0)
		| TVar _ -> "v"
		| TArrow _ -> error "cannot declare variables with function types"
	in
	let var_number = try
			Hashtbl.find var_name_map var_name
		with Not_found -> 0
	in
	Hashtbl.replace var_name_map var_name (var_number + 1) ;
	let var_name = "_" ^ var_name ^ (string_of_int var_number) in
	declare_var var_name ty ;
	var_name




(* not sure if we need this *)
(*
let assert_true if_clause x = match if_clause with
	| None -> Smt.write ("(assert " ^ x ^ ")")
	| Some f -> Smt.write ("(assert (=> " ^ f ^ " " ^ x ^ "))")
*)

let assert_true translated_expr = Smt.write ("(assert " ^ translated_expr ^ ")")

let assert_false translated_expr = Smt.write ("(assert (not " ^ translated_expr ^ "))")

let assert_eq translated_expr1 translated_expr2 =
	assert_true ("(= " ^ translated_expr1 ^ " " ^ translated_expr2 ^ ")")



let rec check_contract if_clause fn_env local_env contract_expr =
	Smt.push_pop (fun () ->
			begin match if_clause with
				| Some translated_cond_expr -> assert_true translated_cond_expr
				| None -> ()
			end ;
			assert_false (check_value Formula if_clause fn_env local_env contract_expr) ;
			match Smt.check_sat () with
				| Unsat -> (* OK *) ()
				| Sat -> error ("SMT solver returned sat.")
				| Unknown -> error ("SMT solver returned unknown.")
				| Error message -> error ("SMT solver returned " ^ message ^ "."))


and check_function_subtype if_clause fn_env local_env fn_expr expected_fn_ty =
	let (closure_local_env, fn_ty) = check_function if_clause fn_env local_env fn_expr in
	let (param_r_ty_list, return_r_ty) = match fn_ty with
		| TArrow(param_r_ty_list, return_r_ty) -> param_r_ty_list, return_r_ty
		| _ -> assert false
	in
	let (expected_param_r_ty_list, expected_return_r_ty) = match expected_fn_ty with
		| TArrow(expected_param_r_ty_list, expected_return_r_ty) ->
				expected_param_r_ty_list, expected_return_r_ty
		| _ -> assert false
	in
	Smt.push_pop (fun () ->
		let (new_closure_local_env, new_local_env) = List.fold_left2
			(fun (closure_local_env, local_env) param_r_ty expected_param_r_ty ->
				let (var_name, new_local_env) = match expected_param_r_ty with
					| Plain ty -> (declare_new_var ty, local_env)
					| Named(name, ty) ->
							let var_name = declare_new_var ty in
							(var_name, LocalEnv.extend name var_name local_env)
					| Refined(name, ty, expr) ->
							let var_name = declare_new_var ty in
							let new_local_env = LocalEnv.extend name var_name local_env in
							assert_true (check_value Formula if_clause fn_env new_local_env expr) ;
							(var_name, new_local_env)
				in
				let new_closure_local_env = match param_r_ty with
					| Plain _ -> closure_local_env
					| Named(name, _) -> LocalEnv.extend name var_name closure_local_env
					| Refined(name, _, expr) ->
							let new_closure_local_env = LocalEnv.extend name var_name closure_local_env in
							check_contract if_clause fn_env new_closure_local_env expr ;
							new_closure_local_env
				in
				(new_closure_local_env, new_local_env))
			(closure_local_env, local_env) param_r_ty_list expected_param_r_ty_list
		in
		let return_var_name = declare_new_var (plain_ty expected_return_r_ty) in
		begin match return_r_ty with
			| Plain _ | Named _ -> ()
			| Refined(name, _, expr) ->
					let closure_return_ty_local_env =
						LocalEnv.extend name return_var_name new_closure_local_env
					in
					assert_true (check_value Formula if_clause fn_env closure_return_ty_local_env expr)
		end ;
		begin match expected_return_r_ty with
			| Plain _ | Named _ -> ()
			| Refined(name, _, expr) ->
					let return_ty_local_env = LocalEnv.extend name return_var_name new_local_env in
					check_contract if_clause fn_env return_ty_local_env expr
		end)



and check_function_call if_clause fn_env local_env fn_expr arg_expr_list =
	let (closure_local_env, fn_ty) = check_function if_clause fn_env local_env fn_expr in
	let (param_r_ty_list, return_r_ty) = match fn_ty with
		| TArrow(param_r_ty_list, return_r_ty) -> param_r_ty_list, return_r_ty
		| _ -> assert false
	in
	let rev_translated_arg_expr_list, new_closure_local_env = List.fold_left2
		(fun (rev_translated_arg_expr_list, closure_local_env) param_r_ty arg_expr ->
			if is_function_ty (plain_ty param_r_ty) then error "not implemented - argument is a function" else
			let (new_closure_local_env, translated_arg_expr) = match param_r_ty with
				| Plain _ -> (closure_local_env, check_value Formula if_clause fn_env local_env arg_expr)
				| Named(name, _) ->
						let translated_arg_expr = check_value Term if_clause fn_env local_env arg_expr in
						(LocalEnv.extend name translated_arg_expr closure_local_env, translated_arg_expr)
				| Refined(name, _, expr) ->
						let translated_arg_expr = check_value Term if_clause fn_env local_env arg_expr in
						let new_closure_local_env = LocalEnv.extend name translated_arg_expr closure_local_env in
						check_contract if_clause fn_env new_closure_local_env expr ;
						(new_closure_local_env, translated_arg_expr)
			in
			(translated_arg_expr :: rev_translated_arg_expr_list, new_closure_local_env))
		([], closure_local_env) param_r_ty_list arg_expr_list
	in
	let translated_arg_expr_list = List.rev rev_translated_arg_expr_list in
	(return_r_ty, translated_arg_expr_list, new_closure_local_env)


and check_value expected_result if_clause fn_env local_env expr =
	assert (not (is_function_ty expr.ty)) ;
	match expr.shape with
		| EVar name -> LocalEnv.lookup name local_env
		| EBool b -> translate_bool b
		| EInt i -> translate_int i
		| ECall({shape = EVar fn_name; ty = _} as fn_expr, arg_expr_list)
			when (StringSet.mem fn_name builtins) || (StringSet.mem fn_name uninterpreted) -> begin
				let (return_r_ty, translated_arg_expr_list, closure_local_env) =
					check_function_call if_clause fn_env local_env fn_expr arg_expr_list
				in
				let translated_expr = translate_builtin_and_uninterpreted fn_name translated_arg_expr_list in
				match expected_result with
					| Formula -> translated_expr
					| Term ->
							let var_name = declare_new_var expr.ty in
							assert_eq var_name translated_expr ;
							var_name
			end
		| ECall(fn_expr, arg_expr_list) -> begin
				let (return_r_ty, translated_arg_expr_list, closure_local_env) =
					check_function_call if_clause fn_env local_env fn_expr arg_expr_list
				in
				match return_r_ty with
					| Plain _ | Named _ -> declare_new_var expr.ty
					| Refined(name, _, contract_expr) ->
							let var_name = declare_new_var expr.ty in
							let return_ty_local_env = LocalEnv.extend name var_name closure_local_env in
							let translated_expr =
								check_value Formula if_clause fn_env return_ty_local_env contract_expr
							in
							assert_true translated_expr ;
							var_name
			end
		| EFun _ -> assert false
		| ELet(var_name, value_expr, body_expr) when not (is_function_ty value_expr.ty) ->
				let translated_value_expr = check_value Formula if_clause fn_env local_env value_expr in
				declare_var var_name value_expr.ty ;
				assert_eq var_name translated_value_expr ;
				check_value expected_result if_clause fn_env local_env body_expr
		| ELet(fn_name, fn_expr, body_expr) (* when is_function_ty fn_expr.ty *) ->
				let local_env_and_ty = check_function if_clause fn_env local_env fn_expr in
				let new_fn_env = FnEnv.extend fn_name local_env_and_ty fn_env in
				check_value expected_result if_clause new_fn_env local_env body_expr
		| EIf(cond_expr, then_expr, else_expr) -> begin
				let translated_cond_expr = check_value Term if_clause fn_env local_env cond_expr in
				let then_if_clause, else_if_clause = match if_clause with
					| None -> (Some translated_cond_expr, Some ("(not " ^ translated_cond_expr ^ ")"))
					| Some translated_old_cond_expr ->
							(
								Some ("(and " ^ translated_old_cond_expr ^ " " ^ translated_cond_expr ^ ")"),
								Some ("(and " ^ translated_old_cond_expr ^ " (not " ^ translated_cond_expr ^ "))")
							)
				in
				let translated_then_expr = check_value Formula then_if_clause fn_env local_env then_expr in
				let translated_else_expr = check_value Formula else_if_clause fn_env local_env else_expr in
				let translated_if_expr =
					"(ite " ^ translated_cond_expr ^
						" " ^ translated_then_expr ^ " " ^ translated_else_expr ^ ")"
				in
				match expected_result with
					| Formula -> translated_if_expr
					| Term ->
							let var_name = declare_new_var expr.ty in
							assert_eq var_name translated_if_expr ;
							var_name
			end
		| ECast(expr, ty, Some contract_expr) ->
				let translated_expr = check_value expected_result if_clause fn_env local_env expr in
				check_contract if_clause fn_env local_env contract_expr ;
				translated_expr
		| ECast(expr, ty, None) -> check_value expected_result if_clause fn_env local_env expr


and check_function if_clause fn_env local_env expr =
	assert (is_function_ty expr.ty) ;
	match expr.shape with
		| EVar name ->
				(*assert (not ((StringSet.mem name builtins) || (StringSet.mem name uninterpreted))) ;*)
				FnEnv.lookup name fn_env
		| EBool _ | EInt _ -> assert false
		| ECall(fn_expr, arg_expr_list) ->
				let (return_r_ty, translated_arg_expr_list, closure_local_env) =
					check_function_call if_clause fn_env local_env fn_expr arg_expr_list
				in
				let return_ty = match return_r_ty with
					| Plain return_ty | Named(_, return_ty) -> return_ty
					| Refined _ -> error "cannot use refined type on an output function"
				in
				assert (is_function_ty return_ty) ;
				(closure_local_env, return_ty)
		| EFun(param_list, maybe_return_r_ty, body_expr) when is_function_ty body_expr.ty ->
				error "not implemented - check_function - function returning a function"
		| EFun(param_list, maybe_return_r_ty, body_expr) ->
				Smt.push_pop (fun () ->
					let param_r_ty_list = List.map
						(function 
							| (name, ty, None) ->
									declare_var name ty ;
									Named(name, ty)
							| (name, ty, Some contract_expr) ->
									declare_var name ty ;
									assert_true (check_value Formula if_clause fn_env local_env contract_expr) ;
									Refined(name, ty, contract_expr))
						param_list
					in
					let return_r_ty = match maybe_return_r_ty with
						| Some (Refined(name, ty, expr)) ->
								let translated_body = check_value Term if_clause fn_env local_env body_expr in
								let return_ty_local_env = LocalEnv.extend name translated_body local_env in
								check_contract if_clause fn_env return_ty_local_env expr ;
								Refined(name, ty, expr)
						| _ ->
								ignore (check_value Formula if_clause fn_env local_env body_expr) ;
								Plain body_expr.ty
					in
					(LocalEnv.empty, TArrow(param_r_ty_list, return_r_ty)))
		| ELet(var_name, value_expr, body_expr) when not (is_function_ty value_expr.ty) ->
				let translated_value_expr = check_value Formula if_clause fn_env local_env value_expr in
				declare_var var_name value_expr.ty ;
				assert_eq var_name translated_value_expr ;
				check_function if_clause fn_env local_env body_expr
		| ELet(fn_name, fn_expr, body_expr) (* when is_function_ty fn_expr.ty *) ->
				let local_env_and_ty = check_function if_clause fn_env local_env fn_expr in
				let new_fn_env = FnEnv.extend fn_name local_env_and_ty fn_env in
				check_function if_clause new_fn_env local_env body_expr
		| EIf _ -> error "cannot use an if statement to select a function"
		| ECast(expr, ty, Some contract_expr) ->
				check_function_subtype if_clause fn_env local_env expr ty ;
				check_contract if_clause fn_env local_env contract_expr ;
				(LocalEnv.empty, ty)
		| ECast(expr, ty, None) ->
				check_function_subtype if_clause fn_env local_env expr ty ;
				(LocalEnv.empty, ty)



let global_fn_env =
	Infer.Env.fold
		(fun fn_name fn_ty fn_env ->
			if not (is_function_ty fn_ty) then
				fn_env
			else
				FnEnv.extend fn_name (LocalEnv.empty, real_ty fn_ty) fn_env)
		Core.env FnEnv.empty



let declare_uninterpreted_function fn_name fn_ty =
	(* Declares an uninterpreted symbol, for example

	     length : forall[t] (a : array[t]) -> (l : int if l >= 0)

	   is translated into

	     (declare-fun length (Other) Int)
	     (assert (forall ((a Other)) (>= (length a) 0)))
	*)
	match real_ty fn_ty with
		| TArrow(param_r_ty_list, return_r_ty) -> begin
				let translated_param_list =
					List.map
						(function
							| Plain _ -> error "all parameters of uninterpreted functions must be named"
							| Named(name, ty) | Refined(name, ty, _) ->
									if is_function_ty ty then
										error "parameters of uninterpreted functions cannot be functions"
									else
										(name, translate_ty ty))
						param_r_ty_list
				in
				if is_function_ty (plain_ty return_r_ty) then
					error "uninterpreted functions cannot return functions" ;
				let translated_return_ty = translate_ty (plain_ty return_r_ty) in
				Smt.write
					("(declare-fun " ^ fn_name ^
						" (" ^ (String.concat " " (List.map snd translated_param_list)) ^ ") " ^
						translated_return_ty ^ ")") ;
				match return_r_ty with
					| Plain _ | Named _ -> ()
					| Refined(name, return_ty, expr) ->
							let translated_param_list_str = String.concat " "
								(List.map (fun (param_name, translated_param_ty) ->
									"(" ^ param_name ^ " " ^ translated_param_ty ^ ")")
								translated_param_list)
							in
							let param_name_list_str = String.concat " " (List.map fst translated_param_list) in
							let result_str = "(" ^ fn_name ^ " " ^ param_name_list_str ^ ")" in
							let local_env = LocalEnv.extend name result_str LocalEnv.empty in
							let translated_expr = check_value Formula None global_fn_env local_env expr in
							Smt.write
								("(assert (forall (" ^ translated_param_list_str ^ ") " ^
									translated_expr ^ "))")
			end
		| _ -> error ("uninterpreted symbol " ^ fn_name ^ " must be a function")



let already_started = ref false
let start () =
	if not !already_started then begin
		already_started := true ;
		Smt.start () ;
		Smt.write "(declare-sort Other)" ;
		StringSet.iter
			(fun fn_name ->
				declare_uninterpreted_function fn_name (Infer.Env.lookup fn_name Core.env))
			uninterpreted ;
		StringSet.iter
			(fun name ->
				let ty = Infer.Env.lookup name Core.env in
				if not (is_function_ty ty) then
					declare_var name ty)
			primitives ;
		Smt.write "; End of global declarations.\n"
	end

let check_expr expr =
	start () ;
	Smt.push_pop
		(fun () -> begin
			if is_function_ty expr.ty then
				ignore (check_function None global_fn_env LocalEnv.empty expr)
			else
				ignore (check_value Formula None global_fn_env LocalEnv.empty expr)
			end)
