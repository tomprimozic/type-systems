open Expr


let current_id = ref 0

let next_id () =
	let id = !current_id in
	current_id := id + 1 ;
	id

let reset_id () = current_id := 0


let new_var level = TVar (ref (Unbound(next_id (), level)))
let new_gen_var () = TVar (ref (Generic(next_id ())))


exception Error of string
let error msg = raise (Error msg)


module Env = struct
	module StringMap = Map.Make (String)
	type env = ty StringMap.t

	let empty : env = StringMap.empty
	let extend env name ty = StringMap.add name ty env
	let lookup env name = StringMap.find name env
end



let occurs_check_adjust_levels tvar_id tvar_level ty =
	let rec f = function
		| TVar {contents = Link ty} -> f ty
		| TVar {contents = Generic _} -> assert false
		| TVar ({contents = Unbound(other_id, other_level)} as other_tvar) ->
				if other_id = tvar_id then
					error "recursive types"
				else
					if other_level > tvar_level then
						other_tvar := Unbound(other_id, tvar_level)
					else
						()
		| TApp(ty, ty_arg_list) ->
				f ty ;
				List.iter f ty_arg_list
		| TArrow(param_ty_list, return_ty) ->
				List.iter f param_ty_list ;
				f return_ty
		| TRecord row -> f row
		| TVariant row -> f row
		| TRowExtend(label_ty_map, rest_ty) ->
				LabelMap.iter (fun _ -> List.iter f) label_ty_map ;
				f rest_ty
		| TConst _ | TRowEmpty -> ()
	in
	f ty


let rec unify ty1 ty2 =
	if ty1 == ty2 then () else
	match (ty1, ty2) with
		| TConst name1, TConst name2 when name1 = name2 -> ()
		| TApp(ty1, ty_arg_list1), TApp(ty2, ty_arg_list2) ->
				unify ty1 ty2 ;
				List.iter2 unify ty_arg_list1 ty_arg_list2
		| TArrow(param_ty_list1, return_ty1), TArrow(param_ty_list2, return_ty2) ->
				List.iter2 unify param_ty_list1 param_ty_list2 ;
				unify return_ty1 return_ty2
		| TVar {contents = Link ty1}, ty2 | ty1, TVar {contents = Link ty2} -> unify ty1 ty2
		| TVar {contents = Unbound(id1, _)}, TVar {contents = Unbound(id2, _)} when id1 = id2 ->
				assert false (* There is only a single instance of a particular type variable. *)
		| TVar ({contents = Unbound(id, level)} as tvar), ty
		| ty, TVar ({contents = Unbound(id, level)} as tvar) ->
				occurs_check_adjust_levels id level ty ;
				tvar := Link ty
		| TRecord row1, TRecord row2 -> unify row1 row2
		| TVariant row1, TVariant row2 -> unify row1 row2
		| TRowEmpty, TRowEmpty -> ()
		| (TRowExtend _ as row1), (TRowExtend _ as row2) -> unify_rows row1 row2
		| TRowEmpty, TRowExtend(label_ty_map, _) | TRowExtend(label_ty_map, _), TRowEmpty ->
				let label, _ = LabelMap.choose label_ty_map in
				error ("row does not contain label " ^ label)
		| _, _ -> error ("cannot unify types " ^ string_of_ty ty1 ^ " and " ^ string_of_ty ty2)

and unify_rows row1 row2 =
	let label_ty_map1, rest_ty1 = match_row_ty row1 in
	let label_ty_map2, rest_ty2 = match_row_ty row2 in

	let rec unify_types ty_list1 ty_list2 = match (ty_list1, ty_list2) with
		| (ty1 :: rest1, ty2 :: rest2) -> unify ty1 ty2 ; unify_types rest1 rest2
		| _ -> (ty_list1, ty_list2)
	in

	(* `missing1` contains all the labels/field types that are in labels2 but not in labels1
	   (and `missing2` vice-versa). *)
	let rec unify_labels missing1 missing2 labels1 labels2 = match (labels1, labels2) with
		| ([], []) -> (missing1, missing2)
		| ([], _) -> (add_distinct_labels missing1 labels2, missing2)
		| (_, []) -> (missing1, add_distinct_labels missing2 labels1)
		| ((label1, ty_list1) :: rest1, (label2, ty_list2) :: rest2) -> begin
				match compare_label label1 label2 with
					| 0 ->
							let missing1, missing2 = match unify_types ty_list1 ty_list2 with
								| ([], []) -> (missing1, missing2)
								| (ty_list1, []) -> (missing1, LabelMap.add label1 ty_list1 missing2)
								| ([], ty_list2) -> (LabelMap.add label2 ty_list2 missing1, missing2)
								| _ -> assert false
							in
							unify_labels missing1 missing2 rest1 rest2
					| x when x < 0 ->
							unify_labels missing1 (LabelMap.add label1 ty_list1 missing2) rest1 labels2
					| x (* when x > 0 *) ->
							unify_labels (LabelMap.add label2 ty_list2 missing1) missing2 labels1 rest2
			end
	in
	let (missing1, missing2) =
		unify_labels LabelMap.empty LabelMap.empty
			(LabelMap.bindings label_ty_map1)
			(LabelMap.bindings label_ty_map2)
	in

	match (LabelMap.is_empty missing1, LabelMap.is_empty missing2) with
		| (true, true) -> unify rest_ty1 rest_ty2
		| (true, false) -> unify rest_ty2 (TRowExtend(missing2, rest_ty1))
		| (false, true) -> unify rest_ty1 (TRowExtend(missing1, rest_ty2))
		| (false, false) ->
				match rest_ty1 with
					| TRowEmpty ->
							(* will result in an error *)
							unify rest_ty1 (TRowExtend(missing1, new_var 0))
					| TVar ({contents = Unbound(_, level)} as tvar_ref) -> begin
							let new_rest_row_var = new_var level in
							unify rest_ty2 (TRowExtend(missing2, new_rest_row_var)) ;
							match !tvar_ref with
								| Link _ -> error "recursive row types"
								| _ -> ()
							;
							unify rest_ty1 (TRowExtend(missing1, new_rest_row_var))
						end
					| _ -> assert false



let rec generalize level = function
	| TVar {contents = Unbound(id, other_level)} when other_level > level ->
			TVar (ref (Generic id))
	| TApp(ty, ty_arg_list) ->
			TApp(generalize level ty, List.map (generalize level) ty_arg_list)
	| TArrow(param_ty_list, return_ty) ->
			TArrow(List.map (generalize level) param_ty_list, generalize level return_ty)
	| TVar {contents = Link ty} -> generalize level ty
	| TRecord row -> TRecord (generalize level row)
	| TVariant row -> TVariant (generalize level row)
	| TRowExtend(label_ty_map, rest_ty) ->
			TRowExtend(LabelMap.map (List.map (generalize level)) label_ty_map, generalize level rest_ty)
	| TVar {contents = Generic _} | TVar {contents = Unbound _} | TConst _ | TRowEmpty as ty -> ty

let instantiate level ty =
	let id_var_map = Hashtbl.create 10 in
	let rec f ty = match ty with
		| TConst _ -> ty
		| TVar {contents = Link ty} -> f ty
		| TVar {contents = Generic id} -> begin
				try
					Hashtbl.find id_var_map id
				with Not_found ->
					let var = new_var level in
					Hashtbl.add id_var_map id var ;
					var
			end
		| TVar {contents = Unbound _} -> ty
		| TApp(ty, ty_arg_list) ->
				TApp(f ty, List.map f ty_arg_list)
		| TArrow(param_ty_list, return_ty) ->
				TArrow(List.map f param_ty_list, f return_ty)
		| TRecord row -> TRecord (f row)
		| TVariant row -> TVariant (f row)
		| TRowEmpty -> ty
		| TRowExtend(label_ty_map, rest_ty) ->
				TRowExtend(LabelMap.map (List.map f) label_ty_map, f rest_ty)
	in
	f ty


let rec match_fun_ty num_params = function
	| TArrow(param_ty_list, return_ty) ->
			if List.length param_ty_list <> num_params then
				error "unexpected number of arguments"
			else
				param_ty_list, return_ty
	| TVar {contents = Link ty} -> match_fun_ty num_params ty
	| TVar ({contents = Unbound(id, level)} as tvar) ->
			let param_ty_list = 
				let rec f = function
					| 0 -> []
					| n -> new_var level :: f (n - 1)
				in
				f num_params
			in
			let return_ty = new_var level in
			tvar := Link (TArrow(param_ty_list, return_ty)) ;
			param_ty_list, return_ty
	| _ -> error "expected a function"


let rec infer env level = function
	| Var name -> begin
			try
				instantiate level (Env.lookup env name)
			with Not_found -> error ("variable " ^ name ^ " not found")
		end
	| Fun(param_list, body_expr) ->
			let param_ty_list = List.map (fun _ -> new_var level) param_list in
			let fn_env = List.fold_left2
				(fun env param_name param_ty -> Env.extend env param_name param_ty)
				env param_list param_ty_list
			in
			let return_ty = infer fn_env level body_expr in
			TArrow(param_ty_list, return_ty)
	| Let(var_name, value_expr, body_expr) ->
			let var_ty = infer env (level + 1) value_expr in
			let generalized_ty = generalize level var_ty in
			infer (Env.extend env var_name generalized_ty) level body_expr
	| Call(fn_expr, arg_list) ->
			let param_ty_list, return_ty =
				match_fun_ty (List.length arg_list) (infer env level fn_expr)
			in
			List.iter2
				(fun param_ty arg_expr -> unify param_ty (infer env level arg_expr))
				param_ty_list arg_list
			;
			return_ty
	| RecordEmpty -> TRecord TRowEmpty
	| RecordSelect(record_expr, label) ->
			(* inlined code for Call of function with type "forall[a r] {label : a | r} -> a" *)
			let rest_row_ty = new_var level in
			let field_ty = new_var level in
			let param_ty = TRecord (TRowExtend(LabelMap.singleton label [field_ty], rest_row_ty)) in
			let return_ty = field_ty in
			unify param_ty (infer env level record_expr) ;
			return_ty
	| RecordRestrict(record_expr, label) ->
			(* inlined code for Call of function with type "forall[a r] {label : a | r} -> {r}" *)
			let rest_row_ty = new_var level in
			let field_ty = new_var level in
			let param_ty = TRecord (TRowExtend(LabelMap.singleton label [field_ty], rest_row_ty)) in
			let return_ty = TRecord rest_row_ty in
			unify param_ty (infer env level record_expr) ;
			return_ty
	| RecordExtend(label_expr_map, record_expr) ->
			let label_ty_map =
				LabelMap.map
					(fun arg_expr_list ->
						List.map (fun arg_expr -> infer env level arg_expr) arg_expr_list
						)
					label_expr_map
			in
			let rest_row_ty = new_var level in
			unify (TRecord rest_row_ty) (infer env level record_expr) ;
			TRecord (TRowExtend(label_ty_map, rest_row_ty))
	| Variant(label, expr) ->
			(* inlined code for Call of function with type "forall [a r] a -> [label : a | r]" *)
			let rest_row_ty = new_var level in
			let variant_ty = new_var level in
			let param_ty = variant_ty in
			let return_ty = TVariant (TRowExtend(LabelMap.singleton label [variant_ty], rest_row_ty)) in
			unify param_ty (infer env level expr) ;
			return_ty
	| Case(expr, cases, None) ->
			let return_ty = new_var level in
			let expr_ty = infer env level expr in
			let cases_row = infer_cases env level return_ty TRowEmpty cases in
			unify expr_ty (TVariant cases_row) ;
			return_ty
	| Case(expr, cases, Some (default_var_name, default_expr)) ->
			let default_variant_ty = new_var level in
			let return_ty =
				infer (Env.extend env default_var_name (TVariant default_variant_ty)) level default_expr
			in
			let expr_ty = infer env level expr in
			let cases_row = infer_cases env level return_ty default_variant_ty cases in
			unify expr_ty (TVariant cases_row) ;
			return_ty

and infer_cases env level return_ty rest_row_ty cases = match cases with
	| [] -> rest_row_ty
	| (label, var_name, expr) :: other_cases ->
			let variant_ty = new_var level in
			unify return_ty (infer (Env.extend env var_name variant_ty) level expr) ;
			let other_cases_row = infer_cases env level return_ty rest_row_ty other_cases in
			TRowExtend(LabelMap.singleton label [variant_ty], other_cases_row)
