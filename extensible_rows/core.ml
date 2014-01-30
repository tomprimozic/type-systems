open Expr
open Infer



let core =
	let core_ref = ref Env.empty in

	let assume name ty_str =
		let ty = Parser.ty_forall_eof Lexer.token (Lexing.from_string ty_str) in
		core_ref := Env.extend !core_ref name ty
	in

	assume "head" "forall[a] list[a] -> a" ;
	assume "tail" "forall[a] list[a] -> list[a]" ;
	assume "nil" "forall[a] list[a]" ;
	assume "cons" "forall[a] (a, list[a]) -> list[a]" ;
	assume "cons_curry" "forall[a] a -> list[a] -> list[a]" ;
	assume "map" "forall[a b] (a -> b, list[a]) -> list[b]" ;
	assume "map_curry" "forall[a b] (a -> b) -> list[a] -> list[b]" ;
	assume "one" "int" ;
	assume "zero" "int" ;
	assume "succ" "int -> int" ;
	assume "plus" "(int, int) -> inc" ;
	assume "eq" "forall[a] (a, a) -> bool" ;
	assume "eq_curry" "forall[a] a -> a -> bool" ;
	assume "not" "bool -> bool" ;
	assume "true" "bool" ;
	assume "false" "bool" ;
	assume "pair" "forall[a b] (a, b) -> pair[a, b]" ;
	assume "pair_curry" "forall[a b] a -> b -> pair[a, b]" ;
	assume "first" "forall[a b] pair[a, b] -> a" ;
	assume "second" "forall[a b] pair[a, b] -> b" ;
	assume "id" "forall[a] a -> a" ;
	assume "const" "forall[a b] a -> b -> a" ;
	assume "apply" "forall[a b] (a -> b, a) -> b" ;
	assume "apply_curry" "forall[a b] (a -> b) -> a -> b" ;
	assume "choose" "forall[a] (a, a) -> a" ;
	assume "choose_curry" "forall[a] a -> a -> a" ;

	!core_ref
