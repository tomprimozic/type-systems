open Expr


(* Utils *)
module StringSet = Set.Make(String)

let string_set_from_list l = List.fold_left (fun set el -> StringSet.add el set) StringSet.empty l
let hashtbl_values h = Hashtbl.fold (fun _ value acc -> value :: acc) h []


(* Operators *)
let binary_operators =
	string_set_from_list ["and"; "or"; "<"; ">"; "<="; ">="; "=="; "!="; "+"; "-"; "*"; "/"; "%"]

let unary_operators =
	string_set_from_list ["not"; "unary-"]


(* Printing types *)
let rec string_of_ty_with_var_names string_of_expr ty =
	let id_name_map = Hashtbl.create 10 in
	let count = ref 0 in
	let next_name () =
		let i = !count in
		incr count ;
		let name = String.make 1 (Char.chr (97 + i mod 26)) ^
			if i >= 26 then string_of_int (i / 26) else ""
		in
		name
	in
	let rec complex_ty = function
		| TArrow(param_r_ty_list, return_r_ty) ->
				let string_of_param_r_ty = function
					| Plain ty -> simple_ty ty
					| Named(name, ty) -> name ^ " : " ^ complex_ty ty
					| Refined(name, ty, expr) ->
							name ^ " : " ^ complex_ty ty ^ " if " ^ string_of_expr expr
				in
				let param_r_ty_list_str = match param_r_ty_list with
					| [Plain ty] -> simple_ty ty
					| _ -> "(" ^ String.concat ", " (List.map string_of_param_r_ty param_r_ty_list) ^ ")"
				in
				let return_r_ty_str = match return_r_ty with
					| Plain ty -> complex_ty ty
					| Named(name, ty) -> "(" ^ name ^ " : " ^ complex_ty ty ^ ")"
					| Refined(name, ty, expr) ->
							"(" ^ name ^ " : " ^ complex_ty ty ^ " if " ^ string_of_expr expr ^ ")"
				in
				param_r_ty_list_str ^ " -> " ^ return_r_ty_str
		| TVar {contents = Link ty} -> complex_ty ty
		| ty -> simple_ty ty
	and simple_ty = function
		| TConst name -> name
		| TApp(name, arg_ty_list) ->
				name ^ "[" ^ String.concat ", " (List.map complex_ty arg_ty_list) ^ "]"
		| TVar {contents = Generic id} -> begin
				try
					Hashtbl.find id_name_map id
				with Not_found ->
					let name = next_name () in
					Hashtbl.add id_name_map id name ;
					name
			end
		| TVar {contents = Unbound(id, _)} ->
				"@unknown" ^ string_of_int id
		| TVar {contents = Link ty} -> simple_ty ty
		| ty -> "(" ^ complex_ty ty ^ ")"
	in
	let ty_str = complex_ty ty in
	if !count > 0 then
		let var_names = hashtbl_values id_name_map in
		((List.sort String.compare var_names), ty_str)
	else
		([], ty_str)


let string_of_ty string_of_expr ty : string =
	let var_names, ty_str = string_of_ty_with_var_names string_of_expr ty in
	match var_names with
		| [] -> ty_str
		| var_names -> "forall[" ^ String.concat " " var_names ^ "] " ^ ty_str

let string_of_ty_ann string_of_expr ty : string =
	let var_names, ty_str = string_of_ty_with_var_names string_of_expr ty in
	match var_names with
		| [] -> ty_str
		| var_names -> "some[" ^ String.concat " " var_names ^ "] " ^ ty_str


(* Printing syntax trees *)
let rec string_of_s_ty ty = string_of_ty string_of_s_expr ty

and string_of_s_ty_ann ty = string_of_ty_ann string_of_s_expr ty

and string_of_s_expr expr : string =
	let rec complex_expr = function
		| SFun(param_list, maybe_return_r_ty, body_expr) ->
				let string_of_param = function
					| (name, None) -> name
					| (name, Some (ty, None)) -> name ^ " : " ^ string_of_s_ty_ann ty
					| (name, Some (ty, Some contract_expr)) ->
							name ^ " : " ^ string_of_s_ty_ann ty ^ " if " ^ complex_expr contract_expr
				in
				let param_list_str = String.concat ", " (List.map string_of_param param_list) in
				let return_r_ty_str = match maybe_return_r_ty with
					| None -> ""
					| Some return_r_ty -> begin
							" : " ^ match return_r_ty with
								| Plain ty ->
										if is_function_ty ty then
											"(" ^ string_of_s_ty_ann ty ^ ")"
										else
											string_of_s_ty_ann ty
								| Named(name, ty) -> "(" ^ name ^ " : " ^ string_of_s_ty_ann ty ^ ")"
								| Refined(name, ty, expr) ->
										"(" ^ name ^ " : " ^ string_of_s_ty_ann ty ^ " if " ^ string_of_s_expr expr ^ ")"
						end
				in
				"fun(" ^ param_list_str ^ ")" ^ return_r_ty_str ^ " -> " ^ complex_expr body_expr
		| SLet(var_name, value_expr, body_expr) ->
				"let " ^ var_name ^ " = " ^ complex_expr value_expr ^ " in " ^ complex_expr body_expr
		| SIf(cond_expr, then_expr, else_expr) ->
				"if " ^ complex_expr cond_expr ^
				" then " ^ complex_expr then_expr ^
				" else " ^ complex_expr else_expr
		| SCast(expr, ty, None) -> simple_expr expr ^ " : " ^ string_of_s_ty_ann ty
		| SCast(expr, ty, Some contract_expr) ->
				simple_expr expr ^ " : " ^ string_of_s_ty_ann ty ^ " if " ^ complex_expr contract_expr
		| expr -> simple_expr expr

	and simple_expr = function
		| SVar name -> name
		| SBool b -> string_of_bool b
		| SInt i -> string_of_int i
		| SCall(SVar op, arg_expr_list) when StringSet.mem op binary_operators -> begin
				match arg_expr_list with
					| [left_expr; right_expr] ->
							"(" ^ simple_expr left_expr ^ " " ^ op ^ " " ^ simple_expr right_expr ^ ")"
					| _ -> failwith ("binary op " ^ op ^ " expects 2 arguments")
			end
		| SCall(SVar op, arg_expr_list) when StringSet.mem op unary_operators -> begin
				match arg_expr_list with
					| [expr] -> "(" ^ (if op = "unary-" then "-" else op) ^ " " ^ simple_expr expr ^ ")"
					| _ -> failwith("unary op " ^ op ^ " expects a single argument")
			end
		| SCall(fn_expr, arg_expr_list) ->
				simple_expr fn_expr ^ "(" ^ String.concat ", " (List.map complex_expr arg_expr_list) ^ ")"
		| expr -> "(" ^ complex_expr expr ^ ")"
	in
	complex_expr expr


(* Printing typed expressions *)

(*let string_of_plain_t_ty ty = string_of_s_ty (duplicate_without_refined_types ty)*)

let rec string_of_t_ty ty = string_of_ty string_of_t_expr ty

and string_of_t_ty_ann ty = string_of_ty_ann string_of_t_expr ty

and string_of_t_expr expr : string =
	let rec complex_expr expr = match expr.shape with
		| EFun(param_list, maybe_return_r_ty, body_expr) ->
				let string_of_param = function
					| (name, ty, None) -> name ^ " : " ^ string_of_t_ty_ann ty
					| (name, ty, Some contract_expr) ->
							name ^ " : " ^ string_of_t_ty_ann ty ^ " if " ^ complex_expr contract_expr
				in
				let param_list_str = String.concat ", " (List.map string_of_param param_list) in
				let return_r_ty_str = match maybe_return_r_ty with
					| None -> ""
					| Some return_r_ty -> begin
							" : " ^ match return_r_ty with
								| Plain ty ->
										if is_function_ty ty then
											"(" ^ string_of_t_ty_ann ty ^ ")"
										else
											string_of_t_ty_ann ty
								| Named(name, ty) -> "(" ^ name ^ " : " ^ string_of_t_ty_ann ty ^ ")"
								| Refined(name, ty, expr) ->
										"(" ^ name ^ " : " ^ string_of_t_ty_ann ty ^ " if " ^ string_of_t_expr expr ^ ")"
						end
				in
				"fun(" ^ param_list_str ^ ")" ^ return_r_ty_str ^ " -> " ^ complex_expr body_expr
		| ELet(var_name, value_expr, body_expr) ->
				"let " ^ var_name ^ " = " ^ complex_expr value_expr ^ " in " ^ complex_expr body_expr
		| EIf(cond_expr, then_expr, else_expr) ->
				"if " ^ complex_expr cond_expr ^
				" then " ^ complex_expr then_expr ^
				" else " ^ complex_expr else_expr
		| ECast(expr, ty, None) -> simple_expr expr ^ " : " ^ string_of_t_ty_ann ty
		| ECast(expr, ty, Some contract_expr) ->
				simple_expr expr ^ " : " ^ string_of_t_ty_ann ty ^ " if " ^ complex_expr contract_expr
		| _ -> simple_expr expr

	and simple_expr expr = match expr.shape with
		| EVar name -> name
		| EBool b -> string_of_bool b
		| EInt i -> string_of_int i
		| ECall({shape=EVar op}, arg_expr_list) when StringSet.mem op binary_operators -> begin
				match arg_expr_list with
					| [left_expr; right_expr] ->
							"(" ^ simple_expr left_expr ^ " " ^ op ^ " " ^ simple_expr right_expr ^ ")"
					| _ -> failwith ("binary op " ^ op ^ " expects 2 arguments")
			end
		| ECall({shape=EVar op}, arg_expr_list) when StringSet.mem op unary_operators -> begin
				match arg_expr_list with
					| [expr] -> "(" ^ (if op = "unary-" then "-" else op) ^ " " ^ simple_expr expr ^ ")"
					| _ -> failwith("unary op " ^ op ^ " expects a single argument")
			end
		| ECall(fn_expr, arg_expr_list) ->
				simple_expr fn_expr ^ "(" ^ String.concat ", " (List.map complex_expr arg_expr_list) ^ ")"
		| _ -> "(" ^ complex_expr expr ^ ")"
	in
	complex_expr expr
