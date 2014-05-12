open Expr
open Printing


(* Utils *)
exception Error of string
let error msg = raise (Error msg)


let current_id = ref 0
let reset_id () = current_id := 0
let next_id () =
	let id = !current_id in
	current_id := id + 1 ;
	id


let new_var level = TVar (ref (Unbound(next_id (), level)))
let new_gen_var () = TVar (ref (Generic (next_id ())))


(* Variable environment *)
module Env = struct
	module StringMap = Map.Make (String)
	type env = t_ty StringMap.t

	let empty : env = StringMap.empty
	let extend name ty env =
		if StringMap.mem name env then error ("duplicate variable name \"" ^ name ^ "\"") else
		StringMap.add name ty env
	let lookup name env = StringMap.find name env

	let map f env = StringMap.map f env
	let fold f env init = StringMap.fold f env init
end




(* Unification *)
let occurs_check_adjust_levels tvar_id tvar_level ty =
	let rec f = function
		| TConst _ -> ()
		| TApp(name, ty_arg_list) -> List.iter f ty_arg_list
		| TArrow(param_r_ty_list, return_r_ty) ->
				let g r_ty = f (plain_ty r_ty) in
				List.iter g param_r_ty_list ; g return_r_ty
		| TVar {contents = Generic _} -> assert false
		| TVar ({contents = Unbound(other_id, other_level)} as other_tvar) ->
				if other_id = tvar_id then
					error "recursive types"
				else if other_level > tvar_level then
					other_tvar := Unbound(other_id, tvar_level)
				else
					()
		| TVar {contents = Link ty} -> f ty
	in
	f ty

let rec unify ty1 ty2 =
	if ty1 == ty2 then () else
	match ty1, ty2 with
		| TConst name1, TConst name2 when name1 = name2 -> ()
		| TApp(name1, ty_arg_list1), TApp(name2, ty_arg_list2) when name1 = name2 ->
				List.iter2 unify ty_arg_list1 ty_arg_list2
		| TArrow(param_r_ty_list1, return_r_ty1), TArrow(param_r_ty_list2, return_r_ty2) ->
				let unify_r_ty r_ty1 r_ty2 = unify (plain_ty r_ty1) (plain_ty r_ty2) in
				List.iter2 unify_r_ty param_r_ty_list1 param_r_ty_list2 ;
				unify_r_ty return_r_ty1 return_r_ty2
		| TVar {contents = Link ty1}, ty2 | ty1, TVar {contents = Link ty2} -> unify ty1 ty2
		| TVar {contents = Unbound(id1, _)}, TVar {contents = Unbound(id2, _)} when id1 = id2 ->
				assert false (* There is only a single instance of a particular type variable. *)
		| TVar ({contents = Unbound(id, level)} as tvar), ty
		| ty, TVar ({contents = Unbound(id, level)} as tvar) ->
				occurs_check_adjust_levels id level ty ;
				tvar := Link ty
		| _, _ -> error ("cannot unify types " ^ string_of_t_ty ty1 ^ " and " ^ string_of_t_ty ty2)


(* Type generalization and type schema instantiation *)
let rec generalize level = function
	| TVar {contents = Unbound(id, other_level)} when other_level > level ->
			TVar (ref (Generic id))
	| TApp(name, arg_ty_list) -> TApp(name, List.map (generalize level) arg_ty_list)
	| TArrow(param_r_ty_list, return_r_ty) ->
			let g = r_ty_map (generalize level) in
			TArrow(List.map g param_r_ty_list, g return_r_ty)
	| TVar {contents = Link ty} -> generalize level ty
	| TConst _ | TVar {contents = Generic _} | TVar {contents = Unbound _} as ty -> ty

let instantiate level ty =
	let id_var_map = Hashtbl.create 10 in
	let rec f = function
		| TApp(name, arg_ty_list) -> TApp(name, List.map f arg_ty_list)
		| TArrow(param_r_ty_list, return_r_ty) ->
				TArrow(List.map (r_ty_map f) param_r_ty_list, r_ty_map f return_r_ty)
		| TVar {contents = Generic id} -> begin
				try
					Hashtbl.find id_var_map id
				with Not_found ->
					let var = new_var level in
					Hashtbl.add id_var_map id var ;
					var
			end
		| TVar {contents = Link ty} -> f ty
		| TConst _ | TVar {contents = Unbound _} as ty -> ty
	in
	f ty


(* Type inference and typed tree construction *)
let rec match_fun_ty num_params = function
	| TArrow(param_r_ty_list, return_r_ty) ->
			if List.length param_r_ty_list <> num_params then
				error "unexpected number of arguments"
			else
				(param_r_ty_list, return_r_ty)
	| TVar ({contents = Unbound(id, level)} as tvar) ->
			let param_r_ty_list =
				let rec f = function
					| 0 -> []
					| n -> Plain (new_var level) :: f (n - 1)
				in
				f num_params
			in
			let return_r_ty = Plain (new_var level) in
			tvar := Link (TArrow(param_r_ty_list, return_r_ty)) ;
			(param_r_ty_list, return_r_ty)
	| TVar {contents = Link ty} -> match_fun_ty num_params ty
	| _ -> error "expected a function"

let rec infer_expr env level = function
	| SVar name ->
			let ty =
				try
					instantiate level (Env.lookup name env)
				with Not_found -> error ("variable " ^ name ^ " not found")
			in
			{shape = EVar name; ty = ty}
	| SBool b -> {shape = EBool b; ty = t_bool}
	| SInt i -> {shape = EInt i; ty = TConst "int"}
	| SCall(fn_s_expr, arg_s_expr_list) ->
			let fn_t_expr = infer_expr env level fn_s_expr in
			let param_r_ty_list, return_r_ty =
				match_fun_ty (List.length arg_s_expr_list) fn_t_expr.ty
			in
			let arg_t_expr_list = List.map2
				(fun param_r_ty arg_s_expr ->
					let arg_t_expr = infer_expr env level arg_s_expr in
					unify (plain_ty param_r_ty) arg_t_expr.ty ;
					arg_t_expr)
				param_r_ty_list arg_s_expr_list
			in
			{shape = ECall(fn_t_expr, arg_t_expr_list); ty = plain_ty return_r_ty}
	| SFun(s_param_list, maybe_return_s_r_ty, body_s_expr) ->
			infer_function env level s_param_list maybe_return_s_r_ty body_s_expr
	| SLet(var_name, value_s_expr, body_s_expr) ->
			let value_t_expr = infer_expr env (level + 1) value_s_expr in
			let generalized_ty = generalize level value_t_expr.ty in
			let new_env = Env.extend var_name generalized_ty env in
			let body_t_expr = infer_expr new_env level body_s_expr in
			{
				shape = ELet(var_name, {shape = value_t_expr.shape; ty = generalized_ty}, body_t_expr);
				ty = body_t_expr.ty
			}
	| SIf(cond_s_expr, then_s_expr, else_s_expr) ->
			let cond_t_expr = infer_expr env level cond_s_expr in
			unify cond_t_expr.ty t_bool ;
			let then_t_expr = infer_expr env level then_s_expr in
			let else_t_expr = infer_expr env level else_s_expr in
			unify then_t_expr.ty else_t_expr.ty ;
			{shape = EIf(cond_t_expr, then_t_expr, else_t_expr); ty = then_t_expr.ty}
	| SCast(s_expr, s_ty, maybe_contract_s_expr) ->
			(* Equivalent to: `(fun (x : ty if contract) -> x)(expr)`. *)
			let t_expr = infer_expr env level s_expr in
			let instantiated_t_ty = instantiate_and_infer_ty env level s_ty in
			let plain_t_ty = strip_refined_types instantiated_t_ty in
			unify plain_t_ty t_expr.ty ;
			let maybe_contract_t_expr = match maybe_contract_s_expr with
				| None -> None
				| Some contract_s_expr -> Some (infer_contract env level contract_s_expr)
			in
			{shape = ECast(t_expr, instantiated_t_ty, maybe_contract_t_expr); ty = plain_t_ty}

and instantiate_and_infer_ty env level ty = infer_ty env level (instantiate level ty)

and infer_ty env level = function
	(* Transforms a s_ty into a t_ty, infering the types of contracts along the way. *)
	| TConst name -> TConst name
	| TApp(name, arg_ty_list) -> TApp(name, List.map (infer_ty env level) arg_ty_list)
	| TArrow(param_s_r_ty_list, return_s_r_ty) ->
			let (new_env, rev_param_t_r_ty_list) = List.fold_left
				(fun (env, rev_param_t_r_ty_list) param_s_r_ty ->
					let new_env, param_t_r_ty = infer_r_ty env level param_s_r_ty in
					(new_env, (param_t_r_ty :: rev_param_t_r_ty_list)))
				(env, []) param_s_r_ty_list
			in
			let param_t_r_ty_list = List.rev rev_param_t_r_ty_list in
			let _, return_t_r_ty = infer_r_ty new_env level return_s_r_ty in
			TArrow(param_t_r_ty_list, return_t_r_ty)
	| TVar {contents = Unbound(id, level)} -> TVar {contents = Unbound(id, level)}
	| TVar {contents = Generic id} -> TVar {contents = Generic id}
	| TVar {contents = Link ty} -> infer_ty env level ty

and infer_contract env level s_expr =
	let t_expr = infer_expr env level s_expr in
	unify t_expr.ty t_bool ;
	t_expr

and infer_r_ty env level = function
	| Plain s_ty -> (env, Plain (infer_ty env level s_ty))
	| Named(name, s_ty) ->
			let t_ty = infer_ty env level s_ty in
			let new_env = Env.extend name (strip_refined_types t_ty) env in
			(new_env, Named(name, t_ty))
	| Refined(name, s_ty, s_expr) ->
			let t_ty = infer_ty env level s_ty in
			let new_env = Env.extend name (strip_refined_types t_ty) env in
			let t_expr = infer_contract new_env level s_expr in
			(new_env, Refined(name, t_ty, t_expr))

and infer_function env level s_param_list maybe_return_s_r_ty body_s_expr =
	let (new_env, rev_t_param_list, rev_param_t_r_ty_list) = List.fold_left
		(fun (env, rev_t_param_list, rev_param_t_r_ty_list) s_param ->
			let (new_env, t_param, param_t_ty) = match s_param with
				| (param_name, None) ->
						let param_t_ty = new_var level in
						let new_env = Env.extend param_name param_t_ty env in
						(new_env, (param_name, param_t_ty, None), param_t_ty)
				| (param_name, Some (param_s_ty, None)) ->
						let param_t_ty = instantiate_and_infer_ty env level param_s_ty in
						let new_env = Env.extend param_name (strip_refined_types param_t_ty) env in
						(new_env, (param_name, param_t_ty, None), param_t_ty)
				| (param_name, Some (param_s_ty, Some contract_s_expr)) ->
						let param_t_ty = instantiate_and_infer_ty env level param_s_ty in
						let new_env = Env.extend param_name (strip_refined_types param_t_ty) env in
						let contract_t_expr = infer_contract new_env level contract_s_expr in
						(new_env, (param_name, param_t_ty, Some contract_t_expr), param_t_ty)
			in
			(new_env, t_param :: rev_t_param_list, (Plain param_t_ty) :: rev_param_t_r_ty_list))
		(env, [], []) s_param_list in
	let t_param_list = List.rev rev_t_param_list in
	let param_t_r_ty_list = List.rev rev_param_t_r_ty_list in
	let body_t_expr = infer_expr new_env level body_s_expr in
	let maybe_return_t_r_ty = match maybe_return_s_r_ty with
		| None -> None
		| Some s_r_ty ->
				let s_ty = plain_ty s_r_ty in
				let instantiated_t_ty = instantiate_and_infer_ty new_env level s_ty in
				let plain_t_ty = strip_refined_types instantiated_t_ty in
				unify plain_t_ty body_t_expr.ty ;
				let t_r_ty = match s_r_ty with
					| Plain _ | Named _ -> Plain instantiated_t_ty
					| Refined(name, _, s_expr) ->
							let return_ty_env = Env.extend name plain_t_ty new_env in
							let t_expr = infer_contract return_ty_env level s_expr in
							Refined(name, instantiated_t_ty, t_expr)
				in
				Some t_r_ty
	in
	{
		shape = EFun(t_param_list, maybe_return_t_r_ty, body_t_expr);
		ty = TArrow(param_t_r_ty_list, Plain body_t_expr.ty)
	}
