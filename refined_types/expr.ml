type name = string

type id = int
type level = int


(* syntax tree *)
type s_ty =
	| STConst of name
	| STApp of name * s_ty list
	| STArrow of s_ty list * s_ty
	| STVar of s_tvar ref
	| STRefined of name * s_ty * s_expr

and s_tvar =
	| SUnbound of id * level
	| SLink of s_ty
	| SGeneric of id

and s_expr =
	| SVar of name
	| SBool of bool
	| SInt of int
	| SCall of s_expr * s_expr list
	| SFun of (name * s_ty option) list * s_ty option * s_expr
	| SLet of name * s_expr * s_expr
	| SIf of s_expr * s_expr * s_expr
	| SCast of s_expr * s_ty


let rec real_s_ty = function 
	| STVar {contents = SLink s_ty} -> real_s_ty s_ty
	| s_ty -> s_ty


(* typed tree *)
type t_ty =
	| TTConst of name
	| TTApp of name * t_ty list
	| TTArrow of t_ty list * t_ty
	| TTVar of t_tvar ref
	| TTRefined of name * t_ty * t_expr

and t_tvar =
	| TUnbound of id * level
	| TLink of t_ty
	| TGeneric of id

and t_expr = {shape : t_expr_shape; ty : t_ty}

and t_expr_shape =
	| TVar of name
	| TBool of bool
	| TInt of int
	| TCall of t_expr * t_expr list
	| TFun of (name * t_ty option) list * t_ty option * t_expr
	| TLet of name * t_expr * t_expr
	| TIf of t_expr * t_expr * t_expr
	| TCast of t_expr * t_ty


let rec basic_t_ty = function
	| TTVar {contents = TLink t_ty} -> basic_t_ty t_ty
	| TTRefined(_, t_ty, _) -> basic_t_ty t_ty
	| t_ty -> t_ty



module StringSet = Set.Make(String)

let binary_operators =
	List.fold_left (fun set el -> StringSet.add el set) StringSet.empty
		["and"; "or"; "<"; ">"; "<="; ">="; "=="; "!="; "+"; "-"; "*"; "/"; "%"]

let unary_operators =
	List.fold_left (fun set el -> StringSet.add el set) StringSet.empty
		["not"; "unary-"]


let rec string_of_ty_with_var_names ty =
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
		| STRefined(name, ty, expr) -> name ^ " : " ^ function_ty ty ^ " if " ^ string_of_expr expr
		| STVar {contents = SLink ty} -> complex_ty ty
		| ty -> function_ty ty
	and function_ty = function
		| STArrow(param_ty_list, return_ty) ->
				let param_ty_list_str = match param_ty_list with
					| [param_ty] -> atomic_ty param_ty
					| _ -> "(" ^ String.concat ", " (List.map complex_ty param_ty_list) ^ ")"
				in
				let return_ty_str = function_ty return_ty in
				param_ty_list_str ^ " -> " ^ return_ty_str
		| STVar {contents = SLink ty} -> function_ty ty
		| ty -> atomic_ty ty
	and atomic_ty = function
		| STConst name -> name
		| STApp(name, ty_arg_list) ->
				name ^ "[" ^ String.concat ", " (List.map complex_ty ty_arg_list) ^ "]"
		| STVar {contents = SGeneric id} -> begin
				try
					Hashtbl.find id_name_map id
				with Not_found ->
					let name = next_name () in
					Hashtbl.add id_name_map id name ;
					name
			end
		| STVar {contents = SUnbound(id, _)} ->
				"@unknown" ^ string_of_int id
		| STVar {contents = SLink ty} -> atomic_ty ty
		| ty -> "(" ^ complex_ty ty ^ ")"
	in
	let ty_str = complex_ty ty in
	if !count > 0 then
		let var_names = Hashtbl.fold (fun _ value acc -> value :: acc) id_name_map [] in
		(List.sort String.compare var_names), ty_str
	else
		[], ty_str

and string_of_ty ty : string =
	let var_names, ty_str = string_of_ty_with_var_names ty in
	if List.length var_names > 0 then
		"forall[" ^ String.concat " " var_names ^ "] " ^ ty_str
	else
		ty_str

and string_of_ty_ann ty : string =
	let var_names, ty_str = string_of_ty_with_var_names ty in
	if List.length var_names > 0 then
		"some[" ^ String.concat " " var_names ^ "] " ^ ty_str
	else
		ty_str

and simple_string_of_ty_ann ty : string =
	let var_names, ty_str = string_of_ty_with_var_names ty in
	let ty_str = match real_s_ty ty with
		| STArrow _ | STRefined _ -> "(" ^ ty_str ^ ")"
		| _ -> ty_str
	in
	if List.length var_names > 0 then
		"some[" ^ String.concat " " var_names ^ "] " ^ ty_str
	else
		ty_str

and function_string_of_ty_ann ty : string =
	let var_names, ty_str = string_of_ty_with_var_names ty in
	let ty_str = match real_s_ty ty with
		| STRefined _ -> "(" ^ ty_str ^ ")"
		| _ -> ty_str
	in
	if List.length var_names > 0 then
		"some[" ^ String.concat " " var_names ^ "] " ^ ty_str
	else
		ty_str

and string_of_expr expr : string =
	let rec complex_expr = function
		| SCast(expr, STRefined("", ty, contract_expr)) ->
				atomic_expr expr ^ " : " ^ simple_string_of_ty_ann ty ^ " if " ^ complex_expr contract_expr
		| SCast(SVar var_name, STRefined(contract_var_name, ty, contract_expr))
				when var_name = contract_var_name ->
					var_name ^ " : " ^ simple_string_of_ty_ann ty ^ " if " ^ complex_expr contract_expr
		| SCast(expr, ty) ->
				atomic_expr expr ^ " : " ^ function_string_of_ty_ann ty
		| SLet(var_name, value_expr, body_expr) ->
				"let " ^ var_name ^ " = " ^ complex_expr value_expr ^ " in " ^ complex_expr body_expr
		| SIf(if_expr, then_expr, else_expr) ->
				"if " ^ complex_expr if_expr ^
				" then " ^ complex_expr then_expr ^
				" else " ^ complex_expr else_expr
		| SFun(param_list, maybe_ret_ty_ann, body_expr) ->
				let param_list_str =
					String.concat ", "
						(List.map
							(fun (param_name, maybe_ty_ann) ->
								match maybe_ty_ann with
									| Some (STRefined(contract_var_name, ty, contract_expr))
											when param_name = contract_var_name ->
												param_name ^ " : " ^ simple_string_of_ty_ann ty ^
													" if " ^ complex_expr contract_expr
									| Some ty_ann -> param_name ^ " : " ^ function_string_of_ty_ann ty_ann
									| None -> param_name)
							param_list)
				in
				let ret_ty_ann_str = match maybe_ret_ty_ann with
					| None -> ""
					| Some ret_ty_ann -> " : " ^ simple_string_of_ty_ann ret_ty_ann
				in
				"fun(" ^ param_list_str ^ ")" ^ ret_ty_ann_str ^ " -> " ^ complex_expr body_expr
		| expr -> simple_expr expr
	and simple_expr expr = atomic_expr expr
	and atomic_expr = function
		| SVar name -> name
		| SInt i -> string_of_int i
		| SBool true -> "true"
		| SBool false -> "false"
		| SCall(SVar op, arg_list) when StringSet.mem op binary_operators -> begin
				match arg_list with
					| [left; right] -> "(" ^ atomic_expr left ^ " " ^ op ^ " " ^ atomic_expr right ^ ")"
					| _ -> failwith ("binary op " ^ op ^ " must have 2 arguments")
			end
		| SCall(SVar op, arg_list) when StringSet.mem op unary_operators -> begin
				match arg_list with
					| [arg] -> "(" ^ (if op = "unary-" then "-" else op) ^ " " ^ atomic_expr arg ^ ")"
					| _ -> failwith("unary op " ^ op ^ " must have a single argument")
			end
		| SCall(fn_expr, arg_list) ->
				atomic_expr fn_expr ^ "(" ^ String.concat ", " (List.map complex_expr arg_list) ^ ")"
		| expr -> "(" ^ complex_expr expr ^ ")"
	in
	complex_expr expr
