%{

open Expr
open Infer

let unary op arg = SCall(SVar op, [arg])
let binary op left right = SCall(SVar op, [left; right])

let replace_ty_constants_with_vars var_name_list ty =
	let env = List.fold_left
		(fun env var_name -> SEnv.extend env var_name (new_gen_s_var ()))
		SEnv.empty var_name_list
	in
	let rec f ty = match ty with
		| STConst name -> begin
				try
					SEnv.lookup env name
				with Not_found -> ty
			end
		| STVar _ -> ty
		| STApp(name, ty_arg_list) ->
				STApp(name, List.map f ty_arg_list)
		| STArrow(param_ty_list, return_ty) ->
				STArrow(List.map f param_ty_list, f return_ty)
		| STRefined(name, ty, expr) ->
				STRefined(name, f ty, expr)
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
	| atomic_expr COLON function_ty               { SCast($1, $3) }
	| atomic_expr COLON simple_ty IF expr         {
				match $1 with
					| SVar name -> SCast($1, STRefined(name, $3, $5))
					| _ -> SCast($1, STRefined("", $3, $5))
			}
	| LET IDENT EQUALS expr IN expr               { SLet($2, $4, $6) }
	| fun_expr                                    { $1 }
	| IF expr THEN expr ELSE expr                 { SIf($2, $4, $6) }

fun_expr:
	| FUN LPAREN param_list RPAREN ARROW expr                   { SFun($3, None, $6) }
	| FUN LPAREN RPAREN ARROW expr                              { SFun([], None, $5) }
	| FUN LPAREN param_list RPAREN COLON simple_ty ARROW expr   { SFun($3, Some $6, $8) }
	| FUN LPAREN RPAREN COLON simple_ty ARROW expr              { SFun([], Some $5, $7) }

boolean_expr:
	| relation_expr                     { $1 }
	| NOT relation_expr                 { unary "not" $2 }
	| relation_expr AND relation_expr   { binary "and" $1 $3 }
	| relation_expr OR relation_expr    { binary "or" $1 $3 }

relation_expr:
	| arithmetic_expr                                   { $1 }
	| arithmetic_expr relation_op arithmetic_expr       { binary $2 $1 $3 }

arithmetic_expr:
	| atomic_expr                               { $1 }
	| MINUS atomic_expr %prec UNARY_MINUS       { unary "unary-" $2 }
	| arithmetic_expr PLUS arithmetic_expr      { binary "+" $1 $3 }
	| arithmetic_expr MINUS arithmetic_expr     { binary "-" $1 $3 }
	| arithmetic_expr STAR arithmetic_expr      { binary "*" $1 $3 }
	| arithmetic_expr SLASH arithmetic_expr     { binary "/" $1 $3 }
	| arithmetic_expr PERCENT arithmetic_expr   { binary "%" $1 $3 }

atomic_expr:
	| IDENT                                             { SVar $1 }
	| INT                                               { SInt $1 }
	| TRUE                                              { SBool true }
	| FALSE                                             { SBool false }
	| LPAREN expr RPAREN                                { $2 }
	| atomic_expr LPAREN expr_comma_list RPAREN         { SCall($1, $3) }
	| atomic_expr LPAREN RPAREN                         { SCall($1, []) }

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

param_list:
	| param                   { [$1] }
	| param COMMA param_list  { $1 :: $3 }

param:
	| IDENT                           { ($1, None) }
	| IDENT COLON function_ty           { ($1, Some $3) }
	| IDENT COLON simple_ty IF expr   { ($1, Some (STRefined($1, $3, $5))) }

ident_list:
	| IDENT               { [$1] }
	| IDENT ident_list    { $1 :: $2 }

ty_forall:
	| ty                                        { $1 }
	| FORALL LBRACKET ident_list RBRACKET ty    { replace_ty_constants_with_vars $3 $5 }

ty:
	| function_ty                           { $1 }
	| IDENT COLON function_ty IF expr       { STRefined($1, $3, $5) }
	| IDENT COLON function_ty               { STRefined($1, $3, SBool true) }

function_ty:
	| atomic_ty                                                   { $1 }
	| LPAREN RPAREN ARROW function_ty                             { STArrow([], $4) }
	| atomic_ty ARROW function_ty                                 { STArrow([$1], $3) }
	| LPAREN ty COMMA ty_comma_list RPAREN ARROW function_ty      { STArrow($2 :: $4, $7) }
	| SOME LBRACKET ident_list RBRACKET function_ty               {
				replace_ty_constants_with_vars $3 $5
			}

simple_ty:
	| atomic_ty                                                 { $1 }
	| SOME LBRACKET ident_list RBRACKET atomic_ty               {
				replace_ty_constants_with_vars $3 $5
			}

atomic_ty:
	| IDENT                                         { STConst $1 }
	| IDENT LBRACKET ty_comma_list RBRACKET         { STApp($1, $3) }
	| LPAREN ty RPAREN                              { $2 }
	
ty_comma_list:
	| ty                        { [$1] }
	| ty COMMA ty_comma_list    { $1 :: $3 }
