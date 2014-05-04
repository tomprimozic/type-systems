type name = string
type id = int
type level = int


(* types *)
type 'a ty =
	| TConst of name
	| TApp of name * 'a ty list
	| TArrow of ('a refined_ty) list * ('a refined_ty)
	| TVar of ('a tvar) ref

and 'a refined_ty = 'a ty * (name  * 'a option) option

and 'a tvar =
	| Unbound of id * level
	| Link of 'a ty
	| Generic of id


let rec get_real_ty = function
	| TVar {contents = Link ty} -> get_real_ty ty
	| ty -> ty


let t_bool = TConst "bool"
let t_int = TConst "int"


(* syntax tree *)
type s_ty = s_expr ty
and s_refined_ty = s_expr refined_ty

and s_expr =
	| SVar of name
	| SBool of bool
	| SInt of int
	| SCall of s_expr * s_expr list
	| SFun of s_param list * s_refined_ty option * s_expr
	| SLet of name * s_expr * s_expr
	| SIf of s_expr * s_expr * s_expr
	| SCast of s_expr * s_ty * s_expr option

and s_param = name * (s_ty * s_expr option) option 


(* typed expressions *)
type t_ty = t_expr ty
and t_refined_ty = t_expr refined_ty

and t_expr = {shape : t_expr_shape; ty : t_ty}

and t_expr_shape =
	| EVar of name
	| EBool of bool
	| EInt of int
	| ECall of t_expr * t_expr list
	| EFun of t_param list * (t_ty * (name * t_expr) option) option * t_expr
	| ELet of name * t_expr * t_expr
	| EIf of t_expr * t_expr * t_expr
	| ECast of t_expr * t_ty * t_expr option

and t_param = name * t_ty * t_expr option



let rec strip_refined_types ty = match ty with
	| TApp(name, param_ty_list) -> TApp(name, List.map strip_refined_types param_ty_list)
	| TVar {contents = Link ty} -> strip_refined_types ty
	| TArrow(param_ty_list, return_ty) ->
			let f (ty, name_and_refined_expr) = (strip_refined_types ty, None) in
			TArrow(List.map f param_ty_list, f return_ty)
	| TConst _ | TVar _ -> ty





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
		| TVar {contents = Link ty} -> complex_ty ty
		| TArrow(param_ty_list, return_ty) ->
				let string_of_param_ty = function
					| ty, None -> simple_ty ty
					| ty, Some (name, None) -> name ^ " : " ^ complex_ty ty
					| ty, Some (name, Some expr) ->
							name ^ " : " ^ complex_ty ty ^ " if " ^ string_of_expr expr
				in
				let param_ty_list_str = match param_ty_list with
					| [param_ty, None] -> simple_ty param_ty
					| _ -> "(" ^ String.concat ", " (List.map string_of_param_ty param_ty_list) ^ ")"
				in
				let return_ty_str = match return_ty with
					| ty, None -> complex_ty ty
					| ty, Some (name, None) -> "(" ^ name ^ " : " ^ complex_ty ty ^ ")"
					| ty, Some (name, Some expr) ->
							"(" ^ name ^ " : " ^ complex_ty ty ^ " if " ^ string_of_expr expr ^ ")"
				in
				param_ty_list_str ^ " -> " ^ return_ty_str
		| ty -> simple_ty ty
	and simple_ty = function
		| TConst name -> name
		| TApp(name, ty_arg_list) ->
				name ^ "[" ^ String.concat ", " (List.map complex_ty ty_arg_list) ^ "]"
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

and string_of_expr expr : string =
	let rec complex_expr = function
		| SCast(expr, ty, None) ->
				simple_expr expr ^ " : " ^ string_of_ty_ann ty
		| SCast(expr, ty, Some refined_expr) ->
				simple_expr expr ^ " : " ^ string_of_ty_ann ty ^ " if " ^ complex_expr refined_expr
		| SLet(var_name, value_expr, body_expr) ->
				"let " ^ var_name ^ " = " ^ complex_expr value_expr ^ " in " ^ complex_expr body_expr
		| SIf(if_expr, then_expr, else_expr) ->
				"if " ^ complex_expr if_expr ^
				" then " ^ complex_expr then_expr ^
				" else " ^ complex_expr else_expr
		| SFun(param_list, maybe_ret_ty_ann, body_expr) ->
				let string_of_param = function
					| name, None -> name
					| name, Some (ty, None) -> name ^ " : " ^ string_of_ty_ann ty
					| name, Some (ty, Some refined_expr) ->
							name ^ " : " ^ string_of_ty_ann ty ^ " if " ^ complex_expr refined_expr
				in
				let param_list_str = String.concat ", " (List.map string_of_param param_list) in
				let ret_ty_ann_str = match maybe_ret_ty_ann with
					| None -> ""
					| Some ret_ty_ann -> begin
							" : " ^ 
							match ret_ty_ann with
								| ty, None -> string_of_ty_ann ty
								| ty, Some (name, None) -> "(" ^ name ^ " : " ^ string_of_ty_ann ty ^ ")"
								| ty, Some (name, Some expr) ->
										"(" ^ name ^ " : " ^ string_of_ty_ann ty ^ " if " ^ string_of_expr expr ^ ")"
						end
				in
				"fun(" ^ param_list_str ^ ")" ^ ret_ty_ann_str ^ " -> " ^ complex_expr body_expr
		| expr -> simple_expr expr
	and simple_expr = function
		| SVar name -> name
		| SInt i -> string_of_int i
		| SBool true -> "true"
		| SBool false -> "false"
		| SCall(SVar op, arg_list) when StringSet.mem op binary_operators -> begin
				match arg_list with
					| [left; right] -> "(" ^ simple_expr left ^ " " ^ op ^ " " ^ simple_expr right ^ ")"
					| _ -> failwith ("binary op " ^ op ^ " must have 2 arguments")
			end
		| SCall(SVar op, arg_list) when StringSet.mem op unary_operators -> begin
				match arg_list with
					| [arg] -> "(" ^ (if op = "unary-" then "-" else op) ^ " " ^ simple_expr arg ^ ")"
					| _ -> failwith("unary op " ^ op ^ " must have a single argument")
			end
		| SCall(fn_expr, arg_list) ->
				simple_expr fn_expr ^ "(" ^ String.concat ", " (List.map complex_expr arg_list) ^ ")"
		| expr -> "(" ^ complex_expr expr ^ ")"
	in
	complex_expr expr




let rec s_ty_of_t_ty ty = match ty with
	| TConst name -> TConst name
	| TApp(name, param_ty_list) -> TApp(name, List.map s_ty_of_t_ty param_ty_list)
	| TVar {contents = Link ty} -> s_ty_of_t_ty ty
	| TVar {contents = Unbound(id, level)} -> TVar {contents = Unbound(id, level)}
	| TVar {contents = Generic id} -> TVar {contents = Generic id}
	| TArrow(param_ty_list, return_ty) ->
			let f (ty, name_and_refined_expr) = (s_ty_of_t_ty ty, None) in
			TArrow(List.map f param_ty_list, f return_ty)

let string_of_plain_ty ty = string_of_ty (s_ty_of_t_ty ty)
