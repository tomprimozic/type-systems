open OUnit2
open Expr

type result =
	| OK of string
	| Fail of string option

let fail = Fail None
let error msg = Fail (Some msg)

let test_cases = [
	(* Hindley-Milner *)
	("id", OK "forall[a] a -> a");
	("1", OK "int");
	("x", error "variable x not found");
	("let x = x in x", error "variable x not found");
	("let x = id in x", OK "forall[a] a -> a");
	("let x = fun(y) -> y in x", OK "forall[a] a -> a");
	("fun x -> x", OK "forall[a] a -> a");
	("fun x -> x", OK "forall[int] int -> int");
	("pair", OK "forall[a b] (a, b) -> pair[a, b]") ;
	("pair", OK "forall[z x] (x, z) -> pair[x, z]") ;
	("fun x -> let y = fun z -> z in y", OK "forall[a b] a -> b -> b");
	("let f = fun x -> x in let id2 = fun y -> y in f == id", OK "bool");
	("let f = fun x -> x in f == succ", OK "bool");
	("let f = fun x -> x in pair(f(1), f(true))", OK "pair[int, bool]");
	("fun f -> pair(f(1), f(true))", fail);
	("let f = fun(x, y) -> let a = x == y in x == y in f", OK "forall[a] (a, a) -> bool");
	("id(id)", OK "forall[a] a -> a");
	("choose(fun(x, y) -> x, fun(x, y) -> y)", OK "forall[a] (a, a) -> a");
	("choose_curry(fun(x, y) -> x)(fun(x, y) -> y)", OK "forall[a] (a, a) -> a");
	("let x = id in let y = let z = x(id) in z in y", OK "forall[a] a -> a");
	("cons(id, nil)", OK "forall[a] list[a -> a]");
	("cons_curry(id)(nil)", OK "forall[a] list[a -> a]");
	("let lst1 = cons(id, nil) in let lst2 = cons(succ, lst1) in lst2", OK "list[int -> int]");
	("cons_curry(id)(cons_curry(succ)(cons_curry(id)(nil)))", OK "list[int -> int]");
	("1 + true", error "cannot unify types int and bool");
	("pair(1)", error "unexpected number of arguments");
	("fun x -> let y = x in y", OK "forall[a] a -> a");
	("fun x -> let y = let z = x(fun w -> w) in z in y", OK "forall[a b] ((a -> a) -> b) -> b");
	("fun x -> fun y -> let z = x(y) in z(y)", OK "forall[a b] (a -> a -> b) -> a -> b");
	("fun x -> let y = fun z -> x(z) in y", OK "forall[a b] (a -> b) -> a -> b");
	("fun x -> let y = fun z -> x in y", OK "forall[a b] a -> b -> a");
	("fun x -> fun y -> let z = x(y) in fun w -> y(w)",
		OK "forall[a b c] ((a -> b) -> c) -> (a -> b) -> a -> b");
	("fun x -> let y = x in y(y)", error "recursive types");
	("fun x -> let y = fun z -> z in y(y)", OK "forall[a b] a -> b -> b");
	("fun x -> x(x)", error "recursive types");
	("1(id)", error "expected a function");
	("fun f -> let x = fun(g, y) -> let m = g(y) in f == g in x",
		OK "forall[a b] (a -> b) -> (a -> b, a) -> bool");
	("let const = fun x -> fun y -> x in const", OK "forall[a b] a -> b -> a");
	("let apply = fun(f, x) -> f(x) in apply", OK "forall[a b] (a -> b, a) -> b");
	("let apply_curry = fun f -> fun x -> f(x) in apply_curry", OK "forall[a b] (a -> b) -> a -> b");

	(* type-checking contracts *)
	("let g = fun(f : int -> int if f(true) == 1) -> 1 in g", error "cannot unify types int and bool");
	("choose(length, length)", OK "forall[a] array[a] -> int");
	("1 : int if 1 > 0", OK "int");
	("1 : int if 1 + 0", error "cannot unify types int and bool");
	("fun(x : some[a] a if x, y : some[a] a) : (z : bool if y) -> x", OK " (bool, bool) -> bool");
	]



let string_of_result = function
	| Fail None -> "Fail"
	| Fail (Some msg) -> "Fail " ^ msg
	| OK ty_str -> "OK " ^ ty_str

let normalize ty_str = string_of_ty (Parser.ty_forall_eof Lexer.token (Lexing.from_string ty_str))

let cmp_result result1 result2 = match (result1, result2) with
	| Fail None, Fail _ | Fail _, Fail None -> true
	| Fail (Some msg1), Fail (Some msg2) -> msg1 = msg2
	| OK ty_str1, OK ty_str2 -> (normalize ty_str1) = (normalize ty_str2)
	| _ -> false

let make_single_test_case (code, expected_result) =
	String.escaped code >:: fun _ ->
		let result =
			try
				Infer.reset_id () ;
				let expr = Parser.expr_eof Lexer.token (Lexing.from_string code) in
				let t_expr = Infer.infer Core.plain_env 0 expr in
				let ty = t_expr.ty in
				let generalized_ty = Infer.generalize (-1) ty in
				OK (string_of_plain_ty generalized_ty)
			with Infer.Error msg ->
				Fail (Some msg)
		in
		assert_equal ~printer:string_of_result ~cmp:cmp_result expected_result result

let suite =
	"test_infer" >::: List.map make_single_test_case test_cases

