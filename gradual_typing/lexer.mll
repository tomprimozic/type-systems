{

open Parser

exception Error

}


let ident = ['_' 'A'-'Z' 'a'-'z'] ['_' 'A'-'Z' 'a'-'z' '0'-'9']*
let integer = ['0'-'9']+

rule token = parse
	| [' ' '\t' '\r' '\n']  { token lexbuf }
	| "fun"                 { FUN }
	| "let"                 { LET }
	| "in"                  { IN }
	| "forall"              { FORALL }
	| ident                 { IDENT (Lexing.lexeme lexbuf) }
	| '('     { LPAREN }
	| ')'     { RPAREN }
	| '['     { LBRACKET }
	| ']'     { RBRACKET }
	| '='     { EQUALS }
	| "->"    { ARROW }
	| ','     { COMMA }
	| eof     { EOF }
	| _       { raise Error }


{

let string_of_token = function
	| FUN -> "fun"
	| LET -> "let"
	| IN -> "in"
	| FORALL -> "forall"
	| IDENT ident -> ident
	| LPAREN -> "("
	| RPAREN -> ")"
	| LBRACKET -> "["
	| RBRACKET -> "]"
	| EQUALS -> "="
	| ARROW -> "->"
	| COMMA -> ","
	| EOF -> "<eof>"

}
