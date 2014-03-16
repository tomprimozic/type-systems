type name = string

type id = int
type level = int

type ty =
	| TConst of name                    (* type constant: `int` or `bool` *)
	| TApp of ty * ty list              (* type application: `list[int]` *)
	| TArrow of ty list * ty            (* function type: `(int, int) -> int` *)
	| TVar of tvar ref                  (* type variable *)
	| TDynamic                          (* dynamic type: `?` *)

and tvar =
	| Unbound of id * level * bool
	| Link of ty
	| Generic of id
	| Bound of id

type expr =
	| Var of name                           (* variable *)
	| Call of expr * expr list              (* application *)
	| Fun of (name * ty option) list * expr             (* abstraction *)
	| Let of name * ty option * expr * expr             (* let *)
	| Ann of expr * ty                      (* type annotation *)






let string_of_ty_with_var_names ty =
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
	let rec complex = function
		| TArrow(param_ty_list, return_ty) ->
				let param_ty_list_str = match param_ty_list with
					| [param_ty] -> simple param_ty
					| _ -> "(" ^ String.concat ", " (List.map complex param_ty_list) ^ ")"
				in
				let return_ty_str = complex return_ty in
				param_ty_list_str ^ " -> " ^ return_ty_str
		| TVar {contents = Link ty} -> complex ty
		| ty -> simple ty
	and simple = function
		| TDynamic -> "?"
		| TConst name -> name
		| TApp(ty, ty_arg_list) ->
				simple ty ^ "[" ^ String.concat ", " (List.map complex ty_arg_list) ^ "]"
		| TVar {contents = Bound id}
		| TVar {contents = Generic id} -> begin
				try
					Hashtbl.find id_name_map id
				with Not_found ->
					let name = next_name () in
					Hashtbl.add id_name_map id name ;
					name
			end
		| TVar {contents = Unbound(id, _, is_dynamic)} ->
				(if is_dynamic then "@dynamic" else "@unknown") ^ string_of_int id
		| TVar {contents = Link ty} -> simple ty
		| ty -> "(" ^ complex ty ^ ")"
	in
	let ty_str = complex ty in
	if !count > 0 then
		let var_names = Hashtbl.fold (fun _ value acc -> value :: acc) id_name_map [] in
		(List.sort String.compare var_names), ty_str
	else
		[], ty_str

let string_of_ty ty : string =
	let var_names, ty_str = string_of_ty_with_var_names ty in
	if List.length var_names > 0 then
		"forall[" ^ String.concat " " var_names ^ "] " ^ ty_str
	else
		ty_str

let string_of_ty_ann ty : string =
	let var_names, ty_str = string_of_ty_with_var_names ty in
	if List.length var_names > 0 then
		"some[" ^ String.concat " " var_names ^ "] " ^ ty_str
	else
		ty_str

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
		| Let(var_name, Some ty_ann, value_expr, body_expr) ->
				"let " ^ var_name ^ " : " ^ string_of_ty_ann ty_ann ^
					" = " ^ complex value_expr ^ " in " ^ complex body_expr
		| Let(var_name, None, value_expr, body_expr) ->
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
