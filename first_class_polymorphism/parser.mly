%{

open Expr
open Infer

let replace_ty_constants_with_vars var_name_list ty =
	let name_map = Hashtbl.create 12 in
	let var_id_list_rev_ref = ref [] in
	List.iter
		(fun var_name -> Hashtbl.replace name_map var_name None)
		var_name_list
	;
	let rec f = function
		| TConst name as ty -> begin
				try
					match Hashtbl.find name_map name with
						| Some var -> var
						| None ->
								let var_id, var = new_bound_var () in
								var_id_list_rev_ref := var_id :: !var_id_list_rev_ref ;
								Hashtbl.replace name_map name (Some var) ;
								var
				with Not_found -> ty
			end
		| TVar _ as ty -> ty
		| TApp(ty, ty_arg_list) ->
				let new_ty = f ty in
				let new_ty_arg_list = List.map f ty_arg_list in
				TApp(new_ty, new_ty_arg_list)
		| TArrow(param_ty_list, return_ty) ->
				let new_param_ty_list = List.map f param_ty_list in
				let new_return_ty = f return_ty in
				TArrow(new_param_ty_list, new_return_ty)
		| TForall(var_id_list, ty) -> TForall(var_id_list, f ty)
	in
	(List.rev !var_id_list_rev_ref, f ty)

%}

%token <string> IDENT
%token FUN LET IN FORALL SOME
%token LPAREN RPAREN LBRACKET RBRACKET
%token ARROW EQUALS COMMA COLON
%token EOF

%start expr_eof
%type <Expr.expr> expr_eof
%start ty_eof
%type <Expr.ty> ty_eof

%%

expr_eof:
	| expr EOF        { $1 }

ty_eof:
	| ty EOF          { $1 }

expr:
	| simple_expr                         { $1 }
	| LET IDENT EQUALS expr IN expr       { Let($2, $4, $6) }
	| FUN ARROW expr                      { Fun([], $3) }
	| FUN param_list ARROW expr           { Fun($2, $4) }
	| simple_expr COLON ty_ann            { Ann($1, $3) }

simple_expr:
	| IDENT                                             { Var $1 }
	| LPAREN expr RPAREN                                { $2 }
	| simple_expr LPAREN expr_comma_list RPAREN         { Call($1, $3) }
	| simple_expr LPAREN RPAREN                         { Call($1, []) }

param_list:
	| param               { [$1] }
	| param param_list    { $1 :: $2 }

param:
	| IDENT                                 { ($1, None) }
	| LPAREN IDENT COLON ty_ann RPAREN      { ($2, Some $4) }

ident_list:
	| IDENT               { [$1] }
	| IDENT ident_list    { $1 :: $2 }

expr_comma_list:
	| expr                          { [$1] }
	| expr COMMA expr_comma_list    { $1 :: $3 }

ty_ann:
	| ty                                     { ([], $1) }
	| SOME LBRACKET ident_list RBRACKET ty   { replace_ty_constants_with_vars $3 $5 }

ty:
	| ty_plain                                        { $1 }
	| FORALL LBRACKET ident_list RBRACKET ty_plain    {
				let (var_id_list, ty) = replace_ty_constants_with_vars $3 $5 in
				match var_id_list with
					| [] -> ty
					| _ -> TForall(var_id_list, ty)
			}

ty_plain:
	| simple_ty                                         { $1 }
	| LPAREN RPAREN ARROW ty                            { TArrow([], $4) }
	| simple_ty ARROW ty                                { TArrow([$1], $3) }
	| LPAREN ty COMMA ty_comma_list RPAREN ARROW ty     { TArrow($2 :: $4, $7) }

simple_ty:
	| IDENT                                         { TConst $1 }
	| simple_ty LBRACKET ty_comma_list RBRACKET     { TApp($1, $3) }
	| LPAREN ty RPAREN                              { $2 }
	
ty_comma_list:
	| ty                        { [$1] }
	| ty COMMA ty_comma_list    { $1 :: $3 }
