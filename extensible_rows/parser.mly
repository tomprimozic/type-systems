%{

open Expr
open Infer


let expr_record_extend label_expr_list record =
	List.fold_left
		(fun record (label, expr) -> RecordExtend(label, expr, record))
		record label_expr_list

let ty_row_extend label_ty_list row =
	List.fold_left
		(fun row (label, ty) -> TRowExtend(label, ty, row))
		row label_ty_list

let replace_ty_constants_with_vars var_name_list ty =
	let env = List.fold_left
		(fun env var_name -> Env.extend env var_name (new_gen_var ()))
		Env.empty var_name_list
	in
	let rec f ty = match ty with
		| TConst name -> begin
				try
					Env.lookup env name
				with Not_found -> ty
			end
		| TVar _ -> ty
		| TApp(ty, ty_arg_list) -> TApp(f ty, List.map f ty_arg_list)
		| TArrow(param_ty_list, return_ty) -> TArrow(List.map f param_ty_list, f return_ty)
		| TRecord row -> TRecord (f row)
		| TRowEmpty -> ty
		| TRowExtend(label, ty, row) -> TRowExtend(label, f ty, f row)
	in
	f ty

%}

%token <string> IDENT
%token FUN LET IN FORALL
%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token ARROW EQUALS COMMA DOT MINUS PIPE COLON
%token EOF

%start expr_eof
%type <Expr.expr> expr_eof
%start ty_eof
%type <Expr.ty> ty_eof
%start ty_forall_eof
%type <Expr.ty> ty_forall_eof

%%

expr_eof:
	| expr EOF        { $1 }

ty_eof:
	| ty EOF          { $1 }

ty_forall_eof:
	| ty_forall EOF   { $1 }

expr:
	| simple_expr                         { $1 }
	| LET IDENT EQUALS expr IN expr       { Let($2, $4, $6) }
	| FUN ident_list ARROW expr           { Fun($2, $4) }

simple_expr:
	| IDENT                                             { Var $1 }
	| LPAREN expr RPAREN                                { $2 }
	| simple_expr LPAREN expr_comma_list RPAREN         { Call($1, $3) }
	| simple_expr LPAREN RPAREN                         { Call($1, []) }
	| LBRACE RBRACE                                     { RecordEmpty }
	| LBRACE record_label_expr_list PIPE expr RBRACE    { expr_record_extend $2 $4 }
	| LBRACE record_label_expr_list RBRACE              { expr_record_extend $2 RecordEmpty }
	| LBRACE expr MINUS IDENT RBRACE                    { RecordRestrict($2, $4) }
	| simple_expr DOT IDENT                             { RecordSelect($1, $3) }

ident_list:
	| IDENT               { [$1] }
	| IDENT ident_list    { $1 :: $2 }

expr_comma_list:
	| expr                          { [$1] }
	| expr COMMA expr_comma_list    { $1 :: $3 }

record_label_expr_list:
	| IDENT EQUALS expr                               { [($1, $3)] }
	| record_label_expr_list COMMA IDENT EQUALS expr  { ($3, $5) :: $1 }

ty_forall:
	| ty                                        { $1 }
	| FORALL LBRACKET ident_list RBRACKET ty    { replace_ty_constants_with_vars $3 $5 }

ty:
	| simple_ty                                         { $1 }
	| LPAREN RPAREN ARROW ty                            { TArrow([], $4) }
	| simple_ty ARROW ty                                { TArrow([$1], $3) }
	| LPAREN ty COMMA ty_comma_list RPAREN ARROW ty     { TArrow($2 :: $4, $7) }

simple_ty:
	| IDENT                                         { TConst $1 }
	| simple_ty LBRACKET ty_comma_list RBRACKET     { TApp($1, $3) }
	| LPAREN ty RPAREN                              { $2 }
	| LBRACE RBRACE                                 { TRecord TRowEmpty }
	| LBRACE IDENT RBRACE                           { TRecord (TConst $2) }
	| LBRACE ty_row PIPE ty RBRACE                  { TRecord (ty_row_extend $2 $4) }
	| LBRACE ty_row RBRACE	                        { TRecord (ty_row_extend $2 TRowEmpty) }
	
ty_comma_list:
	| ty                        { [$1] }
	| ty COMMA ty_comma_list    { $1 :: $3 }

ty_row:
	| IDENT COLON ty                    { [($1, $3)] }
	| ty_row COMMA IDENT COLON ty       { ($3, $5) :: $1 }
