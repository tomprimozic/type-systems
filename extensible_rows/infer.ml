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
		| TRowExtend(label, field_ty, row) -> f field_ty ; f row
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
		| TRowEmpty, TRowEmpty -> ()
		| TRowExtend(label1, field_ty1, rest_row1), (TRowExtend _ as row2) -> begin
				let rest_row1_tvar_ref_option = match rest_row1 with
					| TVar ({contents = Unbound _} as tvar_ref) -> Some tvar_ref
					| _ -> None
				in
				let rest_row2 = rewrite_row row2 label1 field_ty1 in
				begin match rest_row1_tvar_ref_option with
					| Some {contents = Link _} -> error "recursive row types"
					| _ -> ()
				end ;
				unify rest_row1 rest_row2
			end
		| _, _ -> error ("cannot unify types " ^ string_of_ty ty1 ^ " and " ^ string_of_ty ty2)

and rewrite_row row2 label1 field_ty1 = match row2 with
	| TRowEmpty -> error ("row does not contain label " ^ label1)
	| TRowExtend(label2, field_ty2, rest_row2) when label2 = label1 ->
			unify field_ty1 field_ty2 ;
			rest_row2
	| TRowExtend(label2, field_ty2, rest_row2) ->
			TRowExtend(label2, field_ty2, rewrite_row rest_row2 label1 field_ty1)
	| TVar {contents = Link row2} -> rewrite_row row2 label1 field_ty1
	| TVar ({contents = Unbound(id, level)} as tvar) ->
			let rest_row2 = new_var level in
			let ty2 = TRowExtend(label1, field_ty1, rest_row2) in
			tvar := Link ty2 ;
			rest_row2
	| _ -> error "row type expected"



let rec generalize level = function
	| TVar {contents = Unbound(id, other_level)} when other_level > level ->
			TVar (ref (Generic id))
	| TApp(ty, ty_arg_list) ->
			TApp(generalize level ty, List.map (generalize level) ty_arg_list)
	| TArrow(param_ty_list, return_ty) ->
			TArrow(List.map (generalize level) param_ty_list, generalize level return_ty)
	| TVar {contents = Link ty} -> generalize level ty
	| TRecord row -> TRecord (generalize level row)
	| TRowExtend(label, field_ty, row) ->
			TRowExtend(label, generalize level field_ty, generalize level row)
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
		| TRowEmpty -> ty
		| TRowExtend(label, field_ty, row) ->
				TRowExtend(label, f field_ty, f row)
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
			let param_ty = TRecord (TRowExtend(label, field_ty, rest_row_ty)) in
			let return_ty = field_ty in
			unify param_ty (infer env level record_expr) ;
			return_ty
	| RecordRestrict(record_expr, label) ->
			(* inlined code for Call of function with type "forall[a r] {label : a | r} -> {r}" *)
			let rest_row_ty = new_var level in
			let field_ty = new_var level in
			let param_ty = TRecord (TRowExtend(label, field_ty, rest_row_ty)) in
			let return_ty = TRecord rest_row_ty in
			unify param_ty (infer env level record_expr) ;
			return_ty
	| RecordExtend(label, expr, record_expr) ->
			(* inlined code for Call of function with type "forall[a r] (a, {r}) -> {label : a | r}" *)
			let rest_row_ty = new_var level in
			let field_ty = new_var level in
			let param1_ty = field_ty in
			let param2_ty = TRecord rest_row_ty in
			let return_ty = TRecord (TRowExtend(label, field_ty, rest_row_ty)) in
			unify param1_ty (infer env level expr) ;
			unify param2_ty (infer env level record_expr) ;
			return_ty
