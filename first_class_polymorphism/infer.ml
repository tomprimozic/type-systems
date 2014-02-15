open Expr

module IntMap = Map.Make (struct type t = int let compare = compare end)
module StringMap = Map.Make (String)

module HashSet = struct
	type 'a t = ('a, unit) Hashtbl.t
	let create n : 'a t = Hashtbl.create n
	let add set el = Hashtbl.replace set el ()
	let mem set el = Hashtbl.mem set el
end

let int_map_from_2_lists key_list value_list =
	List.fold_left2
		(fun map key value -> IntMap.add key value map)
		IntMap.empty key_list value_list

let int_map_remove_all map key_list =
	List.fold_left
		(fun map key -> IntMap.remove key map)
		map key_list



let current_id = ref 0

let next_id () =
	let id = !current_id in
	current_id := id + 1 ;
	id

let reset_id () = current_id := 0

let new_var level = TVar (ref (Unbound(next_id (), level)))
let new_gen_var () = TVar (ref (Generic(next_id ())))
let new_bound_var () = let id = next_id () in id, TVar (ref (Bound id))


exception Error of string
let error msg = raise (Error msg)


module Env = struct
	type env = ty StringMap.t

	let empty : env = StringMap.empty
	let extend env name ty = StringMap.add name ty env
	let lookup env name = StringMap.find name env
end



let occurs_check_adjust_levels tvar_id tvar_level ty =
	let rec f = function
		| TVar {contents = Link ty} -> f ty
		| TVar {contents = Generic _} | TVar {contents = Bound _} -> ()
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
		| TForall(_, ty) -> f ty
		| TConst _ -> ()
	in
	f ty



let rec substitute_bound_vars var_id_list ty_list ty =
	let rec f id_ty_map = function
		| TConst _ as ty -> ty
		| TVar {contents = Link ty} -> f id_ty_map ty
		| TVar {contents = Bound id} as ty -> begin
				try
					IntMap.find id id_ty_map
				with Not_found -> ty
			end
		| TVar _ as ty -> ty
		| TApp(ty, ty_arg_list) ->
				TApp(f id_ty_map ty, List.map (f id_ty_map) ty_arg_list)
		| TArrow(param_ty_list, return_ty) ->
				TArrow(List.map (f id_ty_map) param_ty_list, f id_ty_map return_ty)
		| TForall(var_id_list, ty) ->
				TForall(var_id_list, f (int_map_remove_all id_ty_map var_id_list) ty)
	in
	f (int_map_from_2_lists var_id_list ty_list) ty



let free_generic_vars ty =
	let free_var_set = HashSet.create 12 in
	let rec f = function
		| TConst _ -> ()
		| TVar {contents = Link ty} -> f ty
		| TVar {contents = Bound _ } -> ()
		| TVar {contents = Generic _ } as ty ->
				HashSet.add free_var_set ty
		| TVar {contents = Unbound _} -> ()
		| TApp(ty, ty_arg_list) ->
				f ty ;
				List.iter f ty_arg_list
		| TArrow(param_ty_list, return_ty) ->
				List.iter f param_ty_list ;
				f return_ty
		| TForall(_, ty) -> f ty
	in
	f ty ;
	free_var_set


let escape_check generic_var_list ty1 ty2 =
	let free_var_set1 = free_generic_vars ty1 in
	let free_var_set2 = free_generic_vars ty2 in
	List.exists
		(fun generic_var ->
			HashSet.mem free_var_set1 generic_var || HashSet.mem free_var_set2 generic_var)
		generic_var_list



let rec unify ty1 ty2 =
	if ty1 == ty2 then () else
	match ty1, ty2 with
		| TConst name1, TConst name2 when name1 = name2 -> ()
		| TApp(ty1, ty_arg_list1), TApp(ty2, ty_arg_list2) ->
				unify ty1 ty2 ;
				List.iter2 unify ty_arg_list1 ty_arg_list2
		| TArrow(param_ty_list1, return_ty1), TArrow(param_ty_list2, return_ty2) ->
				List.iter2 unify param_ty_list1 param_ty_list2 ;
				unify return_ty1 return_ty2
		| TVar {contents = Link ty1}, ty2 | ty1, TVar {contents = Link ty2} -> unify ty1 ty2
		| TVar {contents = Unbound(id1, _)}, TVar {contents = Unbound(id2, _)}
		| TVar {contents = Generic id1}, TVar {contents = Generic id2} when id1 = id2 ->
				(* This should be handled by the `ty1 == ty2` case, as there should
				   be only a single instance of a particular variable. *)
				assert false
		| TVar {contents = Bound _}, _ | _, TVar {contents = Bound _} ->
				(* Bound vars should have been instantiated. *)
				assert false
		| TVar ({contents = Unbound(id, level)} as tvar), ty
		| ty, TVar ({contents = Unbound(id, level)} as tvar) ->
				occurs_check_adjust_levels id level ty ;
				tvar := Link ty
		| (TForall(var_id_list1, ty1) as forall_ty1), (TForall(var_id_list2, ty2) as forall_ty2) ->
				let generic_var_list =
					try
						List.rev_map2 (fun _ _ -> new_gen_var ()) var_id_list1 var_id_list2
					with Invalid_argument _ ->
						error ("cannot unify types " ^ string_of_ty ty1 ^ " and " ^ string_of_ty ty2)
				in
				let generic_ty1 = substitute_bound_vars var_id_list1 generic_var_list ty1 in
				let generic_ty2 = substitute_bound_vars var_id_list2 generic_var_list ty2 in
				unify generic_ty1 generic_ty2 ;
				if escape_check generic_var_list forall_ty1 forall_ty2
				then
					error ("cannot unify types " ^ string_of_ty forall_ty1 ^ " and " ^ string_of_ty forall_ty2)
		| _, _ -> error ("cannot unify types " ^ string_of_ty ty1 ^ " and " ^ string_of_ty ty2)



let substitute_with_new_vars level var_id_list ty =
	let var_list = List.rev_map (fun _ -> new_var level) var_id_list in
	var_list, substitute_bound_vars var_id_list var_list ty

let instantiate_ty_ann level = function
	| [], ty -> [], ty
	| var_id_list, ty -> substitute_with_new_vars level var_id_list ty

let rec instantiate level = function
	| TForall(var_id_list, ty) ->
			let var_list, instantiated_ty = substitute_with_new_vars level var_id_list ty in
			instantiated_ty
	| TVar {contents = Link ty} -> instantiate level ty
	| ty -> ty





let subsume level ty1 ty2 =
	let instantiated_ty2 = instantiate level ty2 in
	match unlink ty1 with
		| TForall(var_id_list1, ty1) as forall_ty1 ->
				let generic_var_list = List.rev_map (fun _ -> new_gen_var ()) var_id_list1 in
				let generic_ty1 = substitute_bound_vars var_id_list1 generic_var_list ty1 in
				unify generic_ty1 instantiated_ty2 ;
				if escape_check generic_var_list forall_ty1 ty2
				then
					error ("type " ^ string_of_ty ty2 ^ " is not an instance of " ^ string_of_ty forall_ty1)
		| ty1 -> unify ty1 instantiated_ty2



let generalize level ty =
	let var_id_list_rev_ref = ref [] in
	let rec f = function
		| TVar {contents = Link ty} -> f ty
		| TVar {contents = Generic _} -> assert false
		| TVar {contents = Bound _} -> ()
		| TVar ({contents = Unbound(other_id, other_level)} as other_tvar) when other_level > level ->
				other_tvar := Bound(other_id) ;
				if not (List.mem other_id !var_id_list_rev_ref) then
					var_id_list_rev_ref := other_id :: !var_id_list_rev_ref
		| TVar {contents = Unbound _} -> ()
		| TApp(ty, ty_arg_list) ->
				f ty ;
				List.iter f ty_arg_list
		| TArrow(param_ty_list, return_ty) ->
				List.iter f param_ty_list ;
				f return_ty
		| TForall(_, ty) -> f ty
		| TConst _ -> ()
	in
	f ty ;
	match !var_id_list_rev_ref with
		| [] -> ty
		| var_id_list_rev -> TForall(List.rev var_id_list_rev, ty)



let rec match_fun_ty num_params = function
	| TArrow(param_ty_list, return_ty) ->
			if List.length param_ty_list <> num_params then
				error "unexpected number of arguments"
			else
				param_ty_list, return_ty
	| TVar {contents = Link ty} -> match_fun_ty num_params ty
	| TVar ({contents = Unbound(id, level)} as tvar) ->
			let param_ty_list = 
				let rec f acc = function
					| 0 -> acc
					| n -> f (new_var level :: acc) (n - 1)
				in
				f [] num_params
			in
			let return_ty = new_var level in
			tvar := Link (TArrow(param_ty_list, return_ty)) ;
			param_ty_list, return_ty
	| _ -> error "expected a function"



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
				error ("polymorphic parameter inferred: "
					^ String.concat ", " (List.map string_of_ty !var_list_ref))
			else
				generalize level (TArrow(param_ty_list, return_ty))
	| Let(var_name, value_expr, body_expr) ->
			let var_ty = infer env (level + 1) value_expr in
			infer (Env.extend env var_name var_ty) level body_expr
	| Call(fn_expr, arg_list) ->
			let fn_ty = instantiate (level + 1) (infer env (level + 1) fn_expr) in
			let param_ty_list, return_ty = match_fun_ty (List.length arg_list) fn_ty in
			infer_args env (level + 1) param_ty_list arg_list ;
			generalize level (instantiate (level + 1) return_ty)
	| Ann(expr, ty_ann) ->
			let _, ty = instantiate_ty_ann level ty_ann in
			let expr_ty = infer env level expr in
			subsume level ty expr_ty ;
			ty

and infer_args env level param_ty_list arg_list =
	let pair_list = List.combine param_ty_list arg_list in
	let get_ordering ty arg =
		(* subsume type variables last *)
		match unlink ty with
				| TVar {contents = Unbound _ } -> 1
				| _ -> 0
	in
	let sorted_pair_list = List.fast_sort
		(fun (ty1, arg1) (ty2, arg2) -> compare (get_ordering ty1 arg1) (get_ordering ty2 arg2))
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
