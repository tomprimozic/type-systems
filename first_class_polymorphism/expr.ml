type name = string

type id = int
type level = int

type ty =
	| TConst of name                    (* type constant: `int` or `bool` *)
	| TApp of ty * ty list              (* type application: `list[int]` *)
	| TArrow of ty list * ty            (* function type: `(int, int) -> int` *)
	| TVar of tvar ref                  (* type variable *)
	| TForall of id list * ty           (* polymorphic type: `forall[a] a -> a` *)

and tvar =
	| Unbound of id * level
	| Link of ty
	| Generic of id
	| Bound of id

let rec unlink = function
	| TVar ({contents = Link ty} as tvar) ->
			let ty = unlink ty in
			tvar := Link ty ;
			ty
	| ty -> ty

let rec is_monomorphic = function
	| TForall _ -> false
	| TConst _ -> true
	| TVar {contents = Link ty} -> is_monomorphic ty
	| TVar _ -> true
	| TApp (ty, ty_arg_list) ->
			is_monomorphic ty && List.for_all is_monomorphic ty_arg_list
	| TArrow(param_ty_list, return_ty) ->
			List.for_all is_monomorphic param_ty_list && is_monomorphic return_ty

type ty_ann = id list * ty             (* type annotation: `some[a b] a -> b` *)

type expr =
	| Var of name                           (* variable *)
	| Call of expr * expr list              (* application *)
	| Fun of (name * ty_ann option) list * expr    (* abstraction *)
	| Let of name * expr * expr             (* let *)
	| Ann of expr * ty_ann                  (* type annotation: `1 : int` *)

let rec is_annotated = function
	| Ann _ -> true
	| Let(_, _, body) -> is_annotated body
	| _ -> false





module IntMap = Map.Make (struct type t = int let compare = compare end)

let name_of_int i =
	let name = String.make 1 (Char.chr (97 + i mod 26)) in
	if i >= 26 then name ^ string_of_int (i / 26) else name

let extend_name_map name_map var_id_list =
	let name_list_rev, name_map =
		List.fold_left
			(fun (name_list, name_map) var_id ->
				let new_name = name_of_int (IntMap.cardinal name_map) in
				new_name :: name_list, IntMap.add var_id new_name name_map)
			([], name_map) var_id_list
	in
	(List.rev name_list_rev, name_map)

let string_of_ty_with_bound_tvars name_map ty =
	let rec complex name_map = function
		| TArrow(param_ty_list, return_ty) ->
				let param_ty_list_str = match param_ty_list with
					| [param_ty] -> simple name_map param_ty
					| _ -> "(" ^ String.concat ", " (List.map (complex name_map) param_ty_list) ^ ")"
				in
				let return_ty_str = complex name_map return_ty in
				param_ty_list_str ^ " -> " ^ return_ty_str
		| TForall(var_id_list, ty) ->
				let name_list, name_map = extend_name_map name_map var_id_list in
				let name_list_str = String.concat " " name_list in
				"forall[" ^ name_list_str ^ "] " ^ complex name_map ty
		| TVar {contents = Link ty} -> complex name_map ty
		| ty -> simple name_map ty
	and simple name_map = function
		| TConst name -> name
		| TApp(ty, ty_arg_list) ->
				let ty_str = simple name_map ty in
				let ty_arg_list_str = String.concat ", " (List.map (complex name_map) ty_arg_list) in
				ty_str ^ "[" ^ ty_arg_list_str ^ "]"
		| TVar {contents = Unbound(id, _)} -> "@unknown" ^ string_of_int id
		| TVar {contents = Bound id} -> IntMap.find id name_map
		| TVar {contents = Generic id} -> "@generic" ^ string_of_int id
		| TVar {contents = Link ty} -> simple name_map ty
		| ty -> "(" ^ complex name_map ty ^ ")"
	in
	complex name_map ty

let string_of_ty ty : string = string_of_ty_with_bound_tvars IntMap.empty ty

let string_of_ty_ann (var_id_list, ty) : string =
	let name_list, name_map = extend_name_map IntMap.empty var_id_list in
	let ty_str = string_of_ty_with_bound_tvars name_map ty in
	match name_list with
		| [] -> ty_str
		| _ -> "some[" ^ String.concat " " name_list ^ "] " ^ ty_str


let string_of_expr expr : string =
	let rec complex = function
		| Fun(param_list, body_expr) ->
				let param_list_str =
					String.concat " "
						(List.map
							(fun (param_name, maybe_ty_ann) ->
								match maybe_ty_ann with
									| Some ty_ann -> "(" ^ param_name ^ " : " ^ string_of_ty_ann ty_ann ^ ")"
									| None -> param_name)
							param_list)
				in
				"fun " ^ param_list_str ^ " -> " ^ complex body_expr
		| Let(var_name, value_expr, body_expr) ->
				"let " ^ var_name ^ " = " ^ complex value_expr ^ " in " ^ complex body_expr
		| Ann(expr, ty_ann) ->
				simple expr ^ " : " ^ string_of_ty_ann ty_ann
		| expr -> simple expr
	and simple = function
		| Var name -> name
		| Call(fn_expr, arg_list) ->
				simple fn_expr ^ "(" ^ String.concat ", " (List.map complex arg_list) ^ ")"
		| expr -> "(" ^ complex expr ^ ")"
	in
	complex expr
