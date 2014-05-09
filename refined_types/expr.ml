type name = string
type id = int
type level = int


(* Types *)
type 'a ty =
	| TConst of name
	| TApp of name * 'a ty list
	| TArrow of ('a refined_ty) list * ('a refined_ty)
	| TVar of ('a tvar) ref

and 'a refined_ty =
	| Plain of 'a ty
	| Named of name * 'a ty
	| Refined of name * 'a ty * 'a

and 'a tvar =
	| Unbound of id * level
	| Link of 'a ty
	| Generic of id


let t_bool = TConst "bool"


let rec real_ty = function
	| TVar {contents = Link ty} -> real_ty ty
	| ty -> ty

let plain_ty = function
	| Plain ty -> ty
	| Named(_, ty) -> ty
	| Refined(_, ty, _) -> ty

let r_ty_map f = function
	| Plain ty -> Plain (f ty)
	| Named(name, ty) -> Named(name, f ty)
	| Refined(name, ty, expr) -> Refined(name, f ty, expr)

let rec is_function_ty = function
	| TArrow _ -> true
	| TVar {contents = Link ty} -> is_function_ty ty
	| _ -> false


let rec strip_refined_types = function
	(* Removes refined types, while preserving type variable identity. *)
	| TApp(name, arg_ty_list) -> TApp(name, List.map strip_refined_types arg_ty_list)
	| TArrow(param_r_ty_list, return_r_ty) ->
			let f r_ty = Plain (strip_refined_types (plain_ty r_ty)) in
			TArrow(List.map f param_r_ty_list, f return_r_ty)
	| TVar {contents = Link ty} -> strip_refined_types ty
	| TConst _ | TVar _ as ty -> ty

let rec duplicate_without_refined_types = function
	(* Removes refined types, duplicating the type (including the type variables). *)
	| TConst name -> TConst name
	| TApp(name, arg_ty_list) ->
			TApp(name, List.map duplicate_without_refined_types arg_ty_list)
	| TArrow(param_r_ty_list, return_r_ty) ->
			let f r_ty = Plain (duplicate_without_refined_types (plain_ty r_ty)) in
			TArrow(List.map f param_r_ty_list, f return_r_ty)
	| TVar {contents = Link ty} -> duplicate_without_refined_types ty
	| TVar {contents = Unbound(id, level)} -> TVar {contents = Unbound(id, level)}
	| TVar {contents = Generic id} -> TVar {contents = Generic id}




(* Syntax tree *)
type s_ty = s_expr ty
and s_refined_ty = s_expr refined_ty

and s_expr =
	| SVar of name
	| SBool of bool
	| SInt of int
	| SCall of s_expr * s_expr list
	| SFun of s_param list * s_refined_ty option * s_expr
	| SLet of name * s_expr * s_expr
	| SIf of s_expr * s_expr * s_expr
	| SCast of s_expr * s_ty * s_expr option

and s_param = name * (s_ty * s_expr option) option 


(* Typed expressions *)
type t_ty = t_expr ty
and t_refined_ty = t_expr refined_ty

and t_expr = {shape : t_expr_shape; ty : t_ty}

and t_expr_shape =
	| EVar of name
	| EBool of bool
	| EInt of int
	| ECall of t_expr * t_expr list
	| EFun of t_param list * t_refined_ty option * t_expr
	| ELet of name * t_expr * t_expr
	| EIf of t_expr * t_expr * t_expr
	| ECast of t_expr * t_ty * t_expr option

and t_param = name * t_ty * t_expr option






