%{

open Expr
open Infer

module StringMap = Map.Make (String)

let unary op arg = SCall(SVar op, [arg])
let binary op left right = SCall(SVar op, [left; right])

let replace_ty_constants_with_vars var_name_list ty =
	let env = List.fold_left
		(fun env var_name -> StringMap.add var_name (new_gen_var ()) env)
		StringMap.empty var_name_list
	in
	let rec f = function
		| TConst name as ty -> begin
				try StringMap.find name env
				with Not_found -> ty
			end
		| TApp(name, arg_ty_list) -> TApp(name, List.map f arg_ty_list)
		| TArrow(param_r_ty_list, return_r_ty) ->
				let g = r_ty_map f in
				TArrow(List.map g param_r_ty_list, g return_r_ty)
		| TVar _ as ty -> ty
	in
	f ty

%}

%token <string> IDENT
%token <int> INT
%token FUN LET REC IN FORALL SOME
%token AND OR NOT IF THEN ELSE TRUE FALSE
%token LPAREN RPAREN LBRACKET RBRACKET
%token ARROW EQUALS COMMA COLON
%token PLUS MINUS STAR SLASH PERCENT
%token GT LT GE LE EQ NE
%token EOF

%left PLUS MINUS
%left STAR SLASH PERCENT
%nonassoc UNARY_MINUS

%start expr_eof
%type <Expr.s_expr> expr_eof
%start ty_eof
%type <Expr.s_ty> ty_eof
%start ty_forall_eof
%type <Expr.s_ty> ty_forall_eof

%%

expr_eof:
	| expr EOF        { $1 }

ty_eof:
	| ty EOF          { $1 }

ty_forall_eof:
	| ty_forall EOF   { $1 }

expr:
	| boolean_expr                                { $1 }
	| simple_expr COLON ty                        { SCast($1, $3, None) }
	| simple_expr COLON ty IF expr                { SCast($1, $3, Some $5) }
	| LET IDENT EQUALS expr IN expr               { SLet($2, $4, $6) }
	| fun_expr                                    { $1 }
	| IF expr THEN expr ELSE expr                 { SIf($2, $4, $6) }

boolean_expr:
	| relation_expr                     { $1 }
	| NOT relation_expr                 { unary "not" $2 }
	| relation_expr AND relation_expr   { binary "and" $1 $3 }
	| relation_expr OR relation_expr    { binary "or" $1 $3 }

relation_expr:
	| arithmetic_expr                                   { $1 }
	| arithmetic_expr relation_op arithmetic_expr       { binary $2 $1 $3 }

arithmetic_expr:
	| simple_expr                               { $1 }
	| MINUS simple_expr %prec UNARY_MINUS       { unary "unary-" $2 }
	| arithmetic_expr PLUS arithmetic_expr      { binary "+" $1 $3 }
	| arithmetic_expr MINUS arithmetic_expr     { binary "-" $1 $3 }
	| arithmetic_expr STAR arithmetic_expr      { binary "*" $1 $3 }
	| arithmetic_expr SLASH arithmetic_expr     { binary "/" $1 $3 }
	| arithmetic_expr PERCENT arithmetic_expr   { binary "%" $1 $3 }

simple_expr:
	| IDENT                                             { SVar $1 }
	| INT                                               { SInt $1 }
	| TRUE                                              { SBool true }
	| FALSE                                             { SBool false }
	| LPAREN expr RPAREN                                { $2 }
	| simple_expr LPAREN expr_comma_list RPAREN         { SCall($1, $3) }
	| simple_expr LPAREN RPAREN                         { SCall($1, []) }

expr_comma_list:
	| expr                          { [$1] }
	| expr COMMA expr_comma_list    { $1 :: $3 }

relation_op:
	| LT    { "<" }
	| GT    { ">" }
	| LE    { "<=" }
	| GE    { ">=" }
	| EQ    { "==" }
	| NE    { "!=" }

fun_expr:
	| FUN IDENT ARROW expr                                      { SFun([($2, None)], None, $4) }
	| FUN LPAREN param_list RPAREN ARROW expr                   { SFun($3, None, $6) }
	| FUN LPAREN RPAREN ARROW expr                              { SFun([], None, $5) }
	| FUN LPAREN param_list RPAREN COLON return_ty ARROW expr   { SFun($3, Some $6, $8) }
	| FUN LPAREN RPAREN COLON return_ty ARROW expr              { SFun([], Some $5, $7) }

param_list:
	| param                   { [$1] }
	| param COMMA param_list  { $1 :: $3 }

param:
	| IDENT                       { ($1, None) }
	| IDENT COLON ty              { ($1, Some ($3, None)) }
	| IDENT COLON ty IF expr      { ($1, Some ($3, Some $5)) }

return_ty:
	| some_simple_ty                          { Plain $1 }
	| LPAREN IDENT COLON ty RPAREN            { Named($2, $4) }
	| LPAREN IDENT COLON ty IF expr RPAREN    { Refined($2, $4, $6) }

ident_list:
	| IDENT               { [$1] }
	| IDENT ident_list    { $1 :: $2 }

ty_forall:
	| ty                                        { $1 }
	| FORALL LBRACKET ident_list RBRACKET ty    { replace_ty_constants_with_vars $3 $5 }

ty:
	| simple_ty                                       { $1 }
	| function_ty                                     { $1 }
	| SOME LBRACKET ident_list RBRACKET ty   {
				replace_ty_constants_with_vars $3 $5
			}

function_ty:
	| LPAREN RPAREN ARROW function_ret_ty                               { TArrow([], $4) }
	| simple_ty ARROW function_ret_ty                                   { TArrow([Plain $1], $3) }
	| LPAREN refined_ty RPAREN ARROW function_ret_ty                    { TArrow([$2], $5) }
	| LPAREN param_ty COMMA param_ty_list RPAREN ARROW function_ret_ty  { TArrow($2 :: $4, $7) }

function_ret_ty:
	| ty                            { Plain $1 }
	| LPAREN refined_ty RPAREN      { $2 }

param_ty_list:
	| param_ty                        { [$1] }
	| param_ty COMMA param_ty_list    { $1 :: $3 }

param_ty:
	| ty                        { Plain $1 }
	| refined_ty                { $1 }

refined_ty:
	| IDENT COLON ty            { Named($1, $3) }
	| IDENT COLON ty IF expr    { Refined($1, $3, $5) }

some_simple_ty:
	| simple_ty                                                 { $1 }
	| SOME LBRACKET ident_list RBRACKET simple_ty               {
				replace_ty_constants_with_vars $3 $5
			}

simple_ty:
	| IDENT                                         { TConst $1 }
	| IDENT LBRACKET ty_comma_list RBRACKET         { TApp($1, $3) }
	| LPAREN ty RPAREN                              { $2 }
	
ty_comma_list:
	| ty                        { [$1] }
	| ty COMMA ty_comma_list    { $1 :: $3 }
