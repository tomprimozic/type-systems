type name = string

let compare_label label1 label2 =
	let compare_length = compare (String.length label1) (String.length label2) in
	if compare_length = 0 then
		String.compare label1 label2
	else compare_length


module LabelMap = Map.Make(
	struct
		type t = name
		let compare = compare_label
	end)

type expr =
	| Var of name                           (* variable *)
	| Call of expr * expr list              (* application *)
	| Fun of name list * expr               (* abstraction *)
	| Let of name * expr * expr             (* let *)
	| RecordSelect of expr * name           (* selecting value of label: `r.a` *)
	| RecordExtend of (expr list) LabelMap.t * expr    (* extending a record: `{a = 1, b = 2 | r}` *)
	| RecordRestrict of expr * name         (* deleting a label: `{r - a}` *)
	| RecordEmpty                           (* empty record: `{}` *)
	| Variant of name * expr                (* new variant value: `:X a` *)
	| Case of expr * (name * name * expr) list * (name * expr) option
			(* a pattern-matching case expression:
					match e {
							:X a -> expr1
						| :Y b -> expr2
						...
						| z -> default_expr (optional)
					}
			*)

type id = int
type level = int

type ty =
	| TConst of name                    (* type constant: `int` or `bool` *)
	| TApp of ty * ty list              (* type application: `list[int]` *)
	| TArrow of ty list * ty            (* function type: `(int, int) -> int` *)
	| TVar of tvar ref                  (* type variable *)
	| TRecord of row                    (* record type: `{...}` *)
	| TVariant of row                   (* variant type: `[...]` *)
	| TRowEmpty                         (* empty row: `<>` *)
	| TRowExtend of (ty list) LabelMap.t * row    (* row extension: `<a : _ , b : _ | ...>` *)

and row = ty    (* the kind of rows - empty row, row variable, or row extension *)

and tvar =
	| Unbound of id * level
	| Link of ty
	| Generic of id


let rec real_ty = function
	| TVar {contents = Link ty} -> real_ty ty
	| ty -> ty

let merge_label_maps label_map1 label_map2 =
	LabelMap.merge
		(fun label maybe_ty_list1 maybe_ty_list2 ->
			match maybe_ty_list1, maybe_ty_list2 with
				| None, None -> assert false
				| None, (Some ty_list2) -> Some ty_list2
				| (Some ty_list1), None -> Some ty_list1
				| (Some ty_list1), (Some ty_list2) -> Some (ty_list1 @ ty_list2))
		label_map1 label_map2

(* Returns a label map with all field types and the type of the "rest",
   which is either a type var or an empty row. *)
let rec match_row_ty = function
	| TRowExtend(label_ty_map, rest_ty) -> begin
			match match_row_ty rest_ty with
				| (rest_label_ty_map, rest_ty) when LabelMap.is_empty rest_label_ty_map ->
						(label_ty_map, rest_ty)
				| (rest_label_ty_map, rest_ty) ->
						(merge_label_maps label_ty_map rest_label_ty_map, rest_ty)
		end
	| TVar {contents = Link ty} -> match_row_ty ty
	| TVar _ as var -> (LabelMap.empty, var)
	| TRowEmpty -> (LabelMap.empty, TRowEmpty)
	| ty -> raise (Failure "not a row")

(* Adds new bindings to a label map. Assumes all bindings (both
   new and existing) are distinct. *)
let add_distinct_labels label_el_map label_el_list =
	List.fold_left
		(fun label_el_map (label, el) ->
			assert (not (LabelMap.mem label label_el_map)) ;
			LabelMap.add label el label_el_map)
	label_el_map label_el_list

let label_map_from_list label_el_list =
	add_distinct_labels LabelMap.empty label_el_list



let string_of_expr expr : string =
	let rec f is_simple = function
		| Var name -> name
		| Call(fn_expr, arg_list) ->
				f true fn_expr ^ "(" ^ String.concat ", " (List.map (f false) arg_list) ^ ")"
		| Fun(param_list, body_expr) ->
				let fun_str =
					"fun " ^ String.concat " " param_list ^ " -> " ^ f false body_expr
				in
				if is_simple then "(" ^ fun_str ^ ")" else fun_str
		| Let(var_name, value_expr, body_expr) ->
				let let_str =
					"let " ^ var_name ^ " = " ^ f false value_expr ^ " in " ^ f false body_expr
				in
				if is_simple then "(" ^ let_str ^ ")" else let_str
		| RecordEmpty -> "{}"
		| RecordSelect(record_expr, label) -> f true record_expr ^ "." ^ label
		| RecordRestrict(record_expr, label) -> "{" ^ f false record_expr ^ " - " ^ label ^ "}"
		| RecordExtend(label_expr_map, rest_expr) ->
				let label_expr_str =
					String.concat ", "
						(List.map
							(fun (label, expr_list) ->
								String.concat ", "
									(List.map (fun expr -> label ^ " = " ^ f false expr) expr_list))
							(LabelMap.bindings label_expr_map))
				in
				let rest_expr_str = match rest_expr with
					| RecordEmpty -> ""
					| expr -> " | " ^ f false expr
				in
				"{" ^ label_expr_str ^ rest_expr_str ^ "}"
		| Variant(label, value) ->
				let variant_str = ":" ^ label ^ " " ^ f true value in
				if is_simple then "(" ^ variant_str ^ ")" else variant_str
		| Case(expr, cases, maybe_default_case) ->
				let cases_str_list = List.map
					(fun (label, var_name, expr) ->
						"| :" ^ label ^ " " ^ var_name ^ " -> " ^ f false expr)
					cases
				in
				let all_cases_str = match (cases_str_list, maybe_default_case) with
					| ([], Some (var_name, expr)) -> var_name ^ " -> " ^ f false expr
					| (cases_str_list, None) -> String.concat "" cases_str_list
					| (cases_str_list, Some (var_name, expr)) ->
							String.concat "" cases_str_list ^ " | " ^ var_name ^ " -> " ^ f false expr
				in
				"match " ^ f false expr ^ " { " ^ all_cases_str ^ " } "
	in
	f false expr

let string_of_ty ty : string =
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
	let rec f is_simple = function
		| TConst name -> name
		| TApp(ty, ty_arg_list) ->
				f true ty ^ "[" ^ String.concat ", " (List.map (f false) ty_arg_list) ^ "]"
		| TArrow(param_ty_list, return_ty) ->
				let arrow_ty_str = match param_ty_list with
					| [param_ty] ->
							let param_ty_str = f true param_ty in
							let return_ty_str = f false return_ty in
							param_ty_str ^ " -> " ^ return_ty_str
					| _ ->
							let param_ty_list_str = String.concat ", " (List.map (f false) param_ty_list) in
							let return_ty_str = f false return_ty in
							"(" ^ param_ty_list_str ^ ") -> " ^ return_ty_str
				in
				if is_simple then "(" ^ arrow_ty_str ^ ")" else arrow_ty_str
		| TVar {contents = Generic id} -> begin
					try
						Hashtbl.find id_name_map id
					with Not_found ->
						let name = next_name () in
						Hashtbl.add id_name_map id name ;
						name
				end
		| TVar {contents = Unbound(id, _)} -> "_" ^ string_of_int id
		| TVar {contents = Link ty} -> f is_simple ty
		| TRecord row_ty -> "{" ^ f false row_ty ^ "}"
		| TVariant row_ty -> "[" ^ f false row_ty ^ "]"
		| TRowEmpty -> ""
		| TRowExtend _ as row_ty ->
				let (label_ty_map, rest_ty) = match_row_ty row_ty in
				let label_ty_str =
					String.concat ", "
						(List.map
							(fun (label, ty_list) ->
								String.concat ", "
									(List.map (fun ty -> label ^ " : " ^ f false ty) ty_list))
							(LabelMap.bindings label_ty_map))
				in
				let rest_ty_str = match real_ty rest_ty with
					| TRowEmpty -> ""
					| TRowExtend _ -> assert false
					| other_ty -> " | " ^ f false other_ty
				in
				label_ty_str ^ rest_ty_str
	in
	let ty_str = f false ty in
	if !count > 0 then
		let var_names = Hashtbl.fold (fun _ value acc -> value :: acc) id_name_map [] in
		"forall[" ^ String.concat " " (List.sort String.compare var_names) ^ "] " ^ ty_str
	else
		ty_str
