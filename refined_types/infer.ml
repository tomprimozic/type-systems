open Expr


let current_id = ref 0

let next_id () =
	let id = !current_id in
	current_id := id + 1 ;
	id

let reset_id () = current_id := 0


let new_s_var level = STVar (ref (SUnbound(next_id (), level)))
let new_gen_s_var () = STVar (ref (SGeneric (next_id ())))

let new_t_var level = TTVar (ref (TUnbound(next_id (), level)))
let new_gen_t_var () = TTVar (ref (TGeneric (next_id ())))


exception Error of string
let error msg = raise (Error msg)


module SEnv = struct
	module StringMap = Map.Make (String)
	type env = s_ty StringMap.t

	let empty : env = StringMap.empty
	let extend env name ty =
		if StringMap.mem name env then error ("duplicate variable name \"" ^ name ^ "\"") else
		StringMap.add name ty env
	let lookup env name = StringMap.find name env
end






let occurs_check_adjust_levels tvar_id tvar_level ty =
	let rec f = function
		| TTVar {contents = TLink ty} -> f ty
		| TTVar {contents = TGeneric _} -> assert false
		| TTVar ({contents = TUnbound(other_id, other_level)} as other_tvar) ->
				if other_id = tvar_id then
					error "recursive types"
				else
					if other_level > tvar_level then
						other_tvar := TUnbound(other_id, tvar_level)
					else
						()
		| TTApp(name, ty_arg_list) ->
				List.iter f ty_arg_list
		| TTArrow(param_ty_list, return_ty) ->
				List.iter f param_ty_list ;
				f return_ty
		| TTConst _ -> ()
		| TTRefined(_, ty, _) -> f ty
	in
	f ty


let rec unify ty1 ty2 =
	if ty1 == ty2 then () else
	match (basic_t_ty ty1, basic_t_ty ty2) with
		| TTConst name1, TTConst name2 when name1 = name2 -> ()
		| TTApp(name1, ty_arg_list1), TTApp(name2, ty_arg_list2) when name1 = name2 ->
				List.iter2 unify ty_arg_list1 ty_arg_list2
		| TTArrow(param_ty_list1, return_ty1), TTArrow(param_ty_list2, return_ty2) ->
				List.iter2 unify param_ty_list1 param_ty_list2 ;
				unify return_ty1 return_ty2
		| TTVar {contents = TLink ty1}, ty2 | ty1, TTVar {contents = TLink ty2} ->
				(* unify ty1 ty2 *)
				assert false
		| TTVar {contents = TUnbound(id1, _)}, TTVar {contents = TUnbound(id2, _)} when id1 = id2 ->
				assert false (* There is only a single instance of a particular type variable. *)
		| TTVar ({contents = TUnbound(id, level)} as tvar), ty
		| ty, TTVar ({contents = TUnbound(id, level)} as tvar) ->
				occurs_check_adjust_levels id level ty ;
				tvar := TLink ty
(*		| _, _ -> error ("cannot unify types " ^ string_of_ty ty1 ^ " and " ^ string_of_ty ty2) *)
		| _, _ -> error "cannot unify types"



let rec match_fun_ty num_params ty = match basic_t_ty ty with
	| TTArrow(param_ty_list, return_ty) ->
			if List.length param_ty_list <> num_params then
				error "unexpected number of arguments"
			else
				param_ty_list, return_ty
	| TTVar ({contents = TUnbound(id, level)} as tvar) ->
			let param_ty_list = 
				let rec f = function
					| 0 -> []
					| n -> new_t_var level :: f (n - 1)
				in
				f num_params
			in
			let return_ty = new_t_var level in
			tvar := TLink (TTArrow(param_ty_list, return_ty)) ;
			param_ty_list, return_ty
	| _ -> error "expected a function"


(*
type t_ty =
	| TTConst of name
	| TTApp of name * t_ty list
	| TTArrow of t_ty list * t_ty
	| TTVar of t_tvar ref
	| TTRefined of name * t_ty * t_expr

and s_expr =
	| SVar of name
	| SBool of bool
	| SInt of int
	| SCall of s_expr * s_expr list
	| SFun of (name * s_ty option) list * s_ty option * s_expr
	| SLet of name * s_expr * s_expr
	| SIf of s_expr * s_expr * s_expr
	| SCast of s_expr * s_ty
*)

let rec typed_expr env = function
	| SVar name -> begin
			let ty =
				try
					SEnv.lookup env name
				with Not_found -> error ("variable " ^ name ^ " not found")
			in
			{shape = TVar name; ty = typed_ty env ty}
		end
	| SBool b -> {shape = TBool b; ty = TTConst "bool"}
	| SInt i -> {shape = TInt i; ty = TTConst "int"}
	| SCall(s_fn_expr, s_arg_list) ->
			let fn_expr = typed_expr env s_fn_expr in
			let arg_list = List.map (typed_expr env) s_arg_list in
			let param_ty_list, return_ty = match_fun_ty (List.length arg_list) fn_expr.ty in
			List.iter2
				(fun param_ty arg_expr -> unify param_ty arg_expr.ty)
				param_ty_list arg_list
			;
			{shape = TCall(fn_expr, arg_list); ty = return_ty}

	| _ -> error "not implemented"


and typed_ty env = function
	| STConst name -> TTConst name
	| STApp(name, ty_args) -> TTApp(name, List.map (typed_ty env) ty_args)
	| _ -> error "not implemented"
