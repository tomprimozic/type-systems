open Expr

type settings = {
	mutable dynamic_parameters : bool;
	mutable freeze_dynamic : bool
}

let settings = {
		dynamic_parameters = true;
		freeze_dynamic = true;
	}



let current_id = ref 0

let next_id () =
	let id = !current_id in
	current_id := id + 1 ;
	id

let reset_id () = current_id := 0


let new_var level is_dynamic = TVar (ref (Unbound(next_id (), level, is_dynamic)))
let new_gen_var () = TVar (ref (Generic (next_id ())))
let new_bound_var () = TVar (ref (Bound (next_id ())))


exception Error of string
let error msg = raise (Error msg)


module Env = struct
	module StringMap = Map.Make (String)
	type env = ty StringMap.t

	let empty : env = StringMap.empty
	let extend env name ty = StringMap.add name ty env
	let lookup env name = StringMap.find name env
end




let occurs_check_adjust_levels_make_vars_dynamic tvar_id tvar_level tvar_is_dynamic ty =
	let rec f = function
		| TVar {contents = Link ty} -> f ty
		| TVar {contents = Generic _ | Bound _} -> assert false
		| TVar ({contents = Unbound(other_id, other_level, other_is_dynamic)} as other_tvar) ->
				if other_id = tvar_id then
					error "recursive types"
				else
						let new_level = min tvar_level other_level in
						let new_is_dynamic = tvar_is_dynamic || other_is_dynamic in
						other_tvar := Unbound(other_id, new_level, new_is_dynamic)
		| TApp(ty, ty_arg_list) ->
				f ty ;
				List.iter f ty_arg_list
		| TArrow(param_ty_list, return_ty) ->
				List.iter f param_ty_list ;
				f return_ty
		| TConst _ -> ()
		| TDynamic -> assert false
	in
	f ty


let rec unify ty1 ty2 =
	if ty1 == ty2 then () else
	match (ty1, ty2) with
		| TConst name1, TConst name2 when name1 = name2 -> ()
		| TDynamic, _ | _, TDynamic -> assert false
		| TApp(ty1, ty_arg_list1), TApp(ty2, ty_arg_list2) ->
				unify ty1 ty2 ;
				List.iter2 unify ty_arg_list1 ty_arg_list2
		| TArrow(param_ty_list1, return_ty1), TArrow(param_ty_list2, return_ty2) ->
				List.iter2 unify param_ty_list1 param_ty_list2 ;
				unify return_ty1 return_ty2
		| TVar {contents = Link ty1}, ty2 | ty1, TVar {contents = Link ty2} -> unify ty1 ty2
		| TVar {contents = Unbound(id1, _, _)}, TVar {contents = Unbound(id2, _, _)} when id1 = id2 ->
				assert false (* There is only a single instance of a particular type variable. *)
		| TVar ({contents = Unbound(id, level, is_dynamic)} as tvar), ty
		| ty, TVar ({contents = Unbound(id, level, is_dynamic)} as tvar) ->
				occurs_check_adjust_levels_make_vars_dynamic id level is_dynamic ty ;
				tvar := Link ty
		| _, _ -> error ("cannot unify types " ^ string_of_ty ty1 ^ " and " ^ string_of_ty ty2)



let rec generalize level = function
	| TDynamic -> assert false
	| TVar {contents = Unbound(id, other_level, is_dynamic)} when other_level > level ->
			if is_dynamic then
				if settings.freeze_dynamic then
					TDynamic
				else
					TVar (ref (Unbound(id, level, true)))
			else
				TVar (ref (Generic id))
	| TApp(ty, ty_arg_list) ->
			TApp(generalize level ty, List.map (generalize level) ty_arg_list)
	| TArrow(param_ty_list, return_ty) ->
			TArrow(List.map (generalize level) param_ty_list, generalize level return_ty)
	| TVar {contents = Link ty} -> generalize level ty
	| TVar {contents = Generic _} | TVar {contents = Unbound _} | TConst _ as ty -> ty
	| TVar {contents = Bound _} -> assert false

let instantiate level ty =
	let id_var_map = Hashtbl.create 10 in
	let rec f ty = match ty with
		| TConst _ -> ty
		| TVar {contents = Link ty} -> f ty
		| TVar {contents = Generic id} -> begin
				try
					Hashtbl.find id_var_map id
				with Not_found ->
					let var = new_var level false in
					Hashtbl.add id_var_map id var ;
					var
			end
		| TDynamic -> new_var level true
		| TVar {contents = Unbound _} -> ty
		| TVar {contents = Bound _} -> assert false
		| TApp(ty, ty_arg_list) ->
				TApp(f ty, List.map f ty_arg_list)
		| TArrow(param_ty_list, return_ty) ->
				TArrow(List.map f param_ty_list, f return_ty)
	in
	f ty

let instantiate_ty_ann level ty =
	let id_var_map = Hashtbl.create 10 in
	let rec f ty = match ty with
		| TConst _ | TDynamic -> ty
		| TVar {contents = Link ty} -> f ty
		| TVar {contents = Generic _} -> assert false
		| TVar {contents = Unbound _} -> ty
		| TVar {contents = Bound id} -> begin
				try
					Hashtbl.find id_var_map id
				with Not_found ->
					let var = new_var level false in
					Hashtbl.add id_var_map id var ;
					var
			end
		| TApp(ty, ty_arg_list) ->
				TApp(f ty, List.map f ty_arg_list)
		| TArrow(param_ty_list, return_ty) ->
				TArrow(List.map f param_ty_list, f return_ty)
	in
	f ty
	


let rec match_fun_ty num_params = function
	| TArrow(param_ty_list, return_ty) ->
			if List.length param_ty_list <> num_params then
				error "unexpected number of arguments"
			else
				param_ty_list, return_ty
	| TVar {contents = Link ty} -> match_fun_ty num_params ty
	| TVar ({contents = Unbound(id, level, is_dynamic)} as tvar) ->
			let param_ty_list = 
				let rec f = function
					| 0 -> []
					| n -> new_var level is_dynamic :: f (n - 1)
				in
				f num_params
			in
			let return_ty = new_var level is_dynamic in
			tvar := Link (TArrow(param_ty_list, return_ty)) ;
			param_ty_list, return_ty
	| TDynamic -> assert false
	| _ -> error "expected a function"


let rec infer env level = function
	| Var name -> begin
			try
				instantiate level (Env.lookup env name)
			with Not_found -> error ("variable " ^ name ^ " not found")
		end
	| Fun(param_list, body_expr) ->
			let fn_env_ref = ref env in
			let param_ty_list = List.map
				(fun (param_name, maybe_param_ty_ann) ->
					let param_ty = match maybe_param_ty_ann with
						| None ->
								if settings.dynamic_parameters
									then TDynamic
									else new_var level false
						| Some ty_ann ->
								instantiate_ty_ann level ty_ann
					in
					fn_env_ref := Env.extend !fn_env_ref param_name param_ty ;
					param_ty)
				param_list in
			let return_ty = infer !fn_env_ref level body_expr in
			TArrow(List.map (instantiate level) param_ty_list, return_ty)
	| Let(var_name, None, value_expr, body_expr) ->
			let var_ty = infer env (level + 1) value_expr in
			let generalized_ty = generalize level var_ty in
			infer (Env.extend env var_name generalized_ty) level body_expr
	| Let(var_name, Some ty_ann, value_expr, body_expr) ->
			(* equivalent to `let var_name = (value_expr : ty_ann) in body_expr` *)
			infer env level (Let(var_name, None, Ann(value_expr, ty_ann), body_expr))
	| Call(fn_expr, arg_list) ->
			let param_ty_list, return_ty =
				match_fun_ty (List.length arg_list) (infer env level fn_expr)
			in
			List.iter2
				(fun param_ty arg_expr -> unify param_ty (infer env level arg_expr))
				param_ty_list arg_list
			;
			return_ty
	| Ann(expr, ty_ann) ->
			(* equivalent to `(fun (x : ty_ann) -> x)(expr)` *)
			infer env level (Call(Fun([("x", Some ty_ann)], Var "x"), [expr]))

