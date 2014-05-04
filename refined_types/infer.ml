open Expr


let current_id = ref 0

let next_id () =
	let id = !current_id in
	current_id := id + 1 ;
	id

let reset_id () = current_id := 0


let new_var level = TVar (ref (Unbound(next_id (), level)))
let new_gen_var () = TVar (ref (Generic (next_id ())))


exception Error of string
let error msg = raise (Error msg)


module Env = struct
	module StringMap = Map.Make (String)
	type env = t_ty StringMap.t

	let empty : env = StringMap.empty
	let extend env name ty =
		if StringMap.mem name env then error ("duplicate variable name \"" ^ name ^ "\"") else
		StringMap.add name ty env
	let lookup env name = StringMap.find name env

	let map = StringMap.map
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
		| TApp(name, ty_arg_list) ->
				List.iter f ty_arg_list
		| TArrow(param_ty_list, return_ty) ->
				let g (ty, _) = f ty in
				List.iter g param_ty_list ;
				g return_ty
		| TConst _ -> ()
	in
	f ty


let rec unify ty1 ty2 =
	if ty1 == ty2 then () else
	match ty1, ty2 with
		| TConst name1, TConst name2 when name1 = name2 -> ()
		| TApp(name1, ty_arg_list1), TApp(name2, ty_arg_list2) when name1 = name2 ->
				List.iter2 unify ty_arg_list1 ty_arg_list2
		| TArrow(param_ty_list1, return_ty1), TArrow(param_ty_list2, return_ty2) ->
				let unify_refined_ty (ty1, _) (ty2, _) = unify ty1 ty2 in
				List.iter2 unify_refined_ty param_ty_list1 param_ty_list2 ;
				unify_refined_ty return_ty1 return_ty2
		| TVar {contents = Link ty1}, ty2 | ty1, TVar {contents = Link ty2} -> unify ty1 ty2
		| TVar {contents = Unbound(id1, _)}, TVar {contents = Unbound(id2, _)} when id1 = id2 ->
				assert false (* There is only a single instance of a particular type variable. *)
		| TVar ({contents = Unbound(id, level)} as tvar), ty
		| ty, TVar ({contents = Unbound(id, level)} as tvar) ->
				occurs_check_adjust_levels id level ty ;
				tvar := Link ty
		| _, _ -> error ("cannot unify types " ^ string_of_plain_ty ty1 ^ " and " ^ string_of_plain_ty ty2)



let rec generalize level = function
	| TVar {contents = Unbound(id, other_level)} when other_level > level ->
			TVar (ref (Generic id))
	| TApp(name, ty_arg_list) ->
			TApp(name, List.map (generalize level) ty_arg_list)
	| TArrow(param_ty_list, return_ty) ->
			let generalize_refined_ty (ty, name_and_refined_expr) =
				(generalize level ty, name_and_refined_expr)
			in
			TArrow(List.map generalize_refined_ty param_ty_list, generalize_refined_ty return_ty)
	| TVar {contents = Link ty} -> generalize level ty
	| TVar {contents = Generic _} | TVar {contents = Unbound _} | TConst _ as ty -> ty

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
		| TApp(name, ty_arg_list) ->
				TApp(name, List.map f ty_arg_list)
		| TArrow(param_ty_list, return_ty) ->
				let g (ty, name_and_refined_expr) = (f ty, name_and_refined_expr) in
				TArrow(List.map g param_ty_list, g return_ty)
	in
	f ty




let rec match_fun_ty num_params = function
	| TArrow(param_ty_list, (return_ty, _)) ->
			if List.length param_ty_list <> num_params then
				error "unexpected number of arguments"
			else
				param_ty_list, return_ty
	| TVar ({contents = Unbound(id, level)} as tvar) ->
			let param_ty_list =
				let rec f = function
					| 0 -> []
					| n -> (new_var level, None) :: f (n - 1)
				in
				f num_params
			in
			let return_ty = new_var level in
			tvar := Link (TArrow(param_ty_list, (return_ty, None))) ;
			param_ty_list, return_ty
	| _ -> error "expected a function"


let rec infer env level = function
	| SVar name -> begin
			let ty =
				try
					instantiate level (Env.lookup env name)
				with Not_found -> error ("variable " ^ name ^ " not found")
			in
			{shape = EVar name; ty = ty}
		end
	| SBool b -> {shape = EBool b; ty = t_bool}
	| SInt i -> {shape = EInt i; ty = t_int}
	| SFun(param_list, maybe_return_ty_ann, body_expr) ->
			let fn_env, rev_t_param_list, rev_param_ty_list = List.fold_left
				(fun (env, rev_t_param_list, rev_param_ty_list) (param_name, maybe_ty_and_refined_expr) ->
					let param_ty = match maybe_ty_and_refined_expr with
						| None -> new_var level
						| Some (param_ty, _) -> infer_refined_type env level (instantiate level param_ty)
					in
					let plain_param_ty = strip_refined_types param_ty in
					let new_env = Env.extend env param_name plain_param_ty in
					let t_maybe_refined_expr = match maybe_ty_and_refined_expr with
						| Some(_, Some refined_expr) ->
								let t_refined_expr = infer new_env level refined_expr in
								unify t_refined_expr.ty t_bool ;
								Some t_refined_expr
						| _ -> None
					in
					(
						new_env,
						(param_name, param_ty, t_maybe_refined_expr) :: rev_t_param_list,
						(plain_param_ty, None) :: rev_param_ty_list
					))
				(env, [], []) param_list in
			let t_param_list = List.rev rev_t_param_list in
			let param_ty_list = List.rev rev_param_ty_list in
			let t_body_expr = infer fn_env level body_expr in
			let return_ty = t_body_expr.ty in
			let t_maybe_return_ty_ann = match maybe_return_ty_ann with
				| None -> None
				| Some (ty, name_and_refined_expr) ->
						let instantiated_ty = infer_refined_type fn_env level (instantiate level ty) in
						let plain_ty = strip_refined_types instantiated_ty in
						unify plain_ty return_ty ;
						let t_maybe_refined_ty = match name_and_refined_expr with
							| Some (name, Some refined_expr) ->
									let return_ty_env = Env.extend fn_env name plain_ty in
									let t_refined_expr = infer return_ty_env level refined_expr in
									unify t_refined_expr.ty t_bool ;
									Some (name, t_refined_expr)
							| _ -> None
						in
						Some (plain_ty, t_maybe_refined_ty)
			in
			{
				shape = EFun(t_param_list, t_maybe_return_ty_ann, t_body_expr);
				ty = TArrow(param_ty_list, (return_ty, None))
			}
	| SCall(fn_expr, arg_list) ->
			let t_fn_expr = infer env level fn_expr in
			let param_ty_list, return_ty = match_fun_ty (List.length arg_list) t_fn_expr.ty in
			let t_arg_list = List.map2
				(fun (param_ty, _) arg_expr ->
					let t_arg_expr = infer env level arg_expr in
					unify param_ty t_arg_expr.ty ;
					t_arg_expr)
				param_ty_list arg_list
			in
			{shape = ECall(t_fn_expr, t_arg_list); ty = return_ty}
	| SLet(var_name, value_expr, body_expr) ->
			let t_value_expr = infer env (level + 1) value_expr in
			let generalized_ty = generalize level t_value_expr.ty in
			let t_body_expr = infer (Env.extend env var_name generalized_ty) level body_expr in
			{
				shape = ELet(var_name, {shape = t_value_expr.shape; ty = generalized_ty}, t_body_expr);
				ty = t_body_expr.ty
			}
	| SIf(if_expr, then_expr, else_expr) ->
			let t_if_expr = infer env level if_expr in
			unify t_if_expr.ty t_bool ;
			let t_then_expr = infer env level then_expr in
			let t_else_expr = infer env level else_expr in
			unify t_then_expr.ty t_else_expr.ty ;
			{shape = EIf(t_if_expr, t_then_expr, t_else_expr); ty = t_then_expr.ty}
	| SCast(expr, ty, maybe_refined_expr) ->
			(* equivalent to `(fun (x : ty if expr) -> x)(expr) *)
			let t_expr = infer env level expr in
			let instantiated_ty = infer_refined_type env level (instantiate level ty) in
			let plain_ty = strip_refined_types instantiated_ty in
			unify plain_ty t_expr.ty ;
			let t_maybe_refined_expr = match maybe_refined_expr with
				| None -> None
				| Some refined_expr ->
						let t_refined_expr = infer env level refined_expr in
						unify t_refined_expr.ty t_bool ;
						Some t_refined_expr
			in
			{shape = ECast(t_expr, instantiated_ty, t_maybe_refined_expr); ty = plain_ty}

and infer_refined_type env level = function
	| TConst name -> TConst name
	| TApp(name, param_ty_list) -> TApp(name, List.map (infer_refined_type env level) param_ty_list)
	| TVar {contents = Link ty} -> infer_refined_type env level ty
	| TVar {contents = Unbound(id, level)} -> TVar {contents = Unbound(id, level)}
	| TVar {contents = Generic id} -> TVar {contents = Generic id}
	| TArrow(param_ty_list, return_ty) ->
			let f env (ty, name_and_refined_expr) =
				let ty = infer_refined_type env level ty in
				let new_env = match name_and_refined_expr with
					| Some (name, _) -> Env.extend env name (strip_refined_types ty)
					| _ -> env
				in
				let t_name_and_refined_expr = match name_and_refined_expr with
					| None -> None
					| Some (name, None) -> Some (name, None)
					| Some (name, Some refined_expr) ->
							let t_refined_expr = infer new_env level refined_expr in
							unify t_refined_expr.ty t_bool ;
							Some (name, Some (t_refined_expr))
				in
				(new_env, (ty, t_name_and_refined_expr))
			in
			let new_env, rev_t_param_ty_list = List.fold_left
				(fun (env, rev_t_param_ty_list) param_ty ->
					let new_env, t_param_ty = f env param_ty in
					(new_env, t_param_ty :: rev_t_param_ty_list))
				(env, []) param_ty_list
			in
			let t_param_ty_list = List.rev rev_t_param_ty_list in
			let _, t_return_ty = f new_env return_ty in
			TArrow(t_param_ty_list, t_return_ty)
