open Expr
open Infer

let rec infer env level = function
	| Var name -> begin
			try
				Env.lookup env name
			with Not_found -> error ("variable " ^ name ^ " not found")
		end
	| Fun(param_list, body_expr) ->
			let fn_env_ref = ref env in
			let var_list_ref = ref [] in
			let param_ty_list = List.map
				(fun (param_name, maybe_param_ty_ann) ->
					let param_ty = match maybe_param_ty_ann with
						| None -> (* equivalent to `some[a] a` *)
								let var = new_var (level + 1) in
								var_list_ref := var :: !var_list_ref ;
								var
						| Some ty_ann ->
								let var_list, ty = instantiate_ty_ann (level + 1) ty_ann in
								var_list_ref := var_list @ !var_list_ref ;
								ty
					in
					fn_env_ref := Env.extend !fn_env_ref param_name param_ty ;
					param_ty)
				param_list
			in
			let inferred_return_ty = infer !fn_env_ref (level + 1) body_expr in
			let return_ty =
				if is_annotated body_expr then inferred_return_ty
				else instantiate (level + 1) inferred_return_ty in
			if not (List.for_all is_monomorphic !var_list_ref) then
				error ("polymorphic parameter inferred: ["
					^ String.concat ", " (List.map string_of_ty !var_list_ref) ^ "]")
			else
				generalize level (TArrow(param_ty_list, return_ty))
	| Let(var_name, value_expr, body_expr) ->
			let var_ty = infer env (level + 1) value_expr in
			infer (Env.extend env var_name var_ty) level body_expr
	| Call(fn_expr, arg_list) ->
			let fn_ty = instantiate (level + 1) (infer env (level + 1) fn_expr) in
			let param_ty_list, return_ty = match_fun_ty (List.length arg_list) fn_ty in
			infer_args env (level + 1) param_ty_list arg_list ;
			generalize level return_ty
	| Ann(expr, ty_ann) ->
			let _, ty = instantiate_ty_ann level ty_ann in
			let expr_ty = infer env level expr in
			subsume level ty expr_ty ;
			ty

and infer_args env level param_ty_list arg_list =
	let pair_list = List.combine param_ty_list arg_list in
	let sorted_pair_list = List.fast_sort
		(* subsume type variables last *)
		(fun (ty1, _) (ty2, _) -> match (unlink ty1, unlink ty2) with
			| TVar {contents = Unbound _}, TVar {contents = Unbound _} -> 0
			| TVar {contents = Unbound _}, _ -> 1
			| _, TVar {contents = Unbound _} -> -1
			| _, _ ->  0)
		pair_list
	in
	List.iter
		(fun (param_ty, arg_expr) ->
			let arg_ty = infer env level arg_expr in
			if is_annotated arg_expr then
				unify param_ty arg_ty
			else
				subsume level param_ty arg_ty)
		sorted_pair_list
