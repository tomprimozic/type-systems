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
	("one", OK "int");
	("x", error "variable x not found");
	("let x = x in x", error "variable x not found");
	("let x = id in x", OK "forall[a] a -> a");
	("let x = fun y -> y in x", OK "forall[a] a -> a");
	("fun x -> x", OK "forall[a] a -> a");
	("pair", OK "forall[a b] (a, b) -> pair[a, b]") ;
	("fun x -> let y = fun z -> z in y", OK "forall[a b] a -> b -> b");
	("let f = fun x -> x in let id = fun y -> y in eq(f, id)", OK "bool");
	("let f = fun x -> x in let id = fun y -> y in eq_curry(f)(id)", OK "bool");
	("let f = fun x -> x in eq(f, succ)", OK "bool");
	("let f = fun x -> x in eq_curry(f)(succ)", OK "bool");
	("let f = fun x -> x in pair(f(one), f(true))", OK "pair[int, bool]");
	("fun f -> pair(f(one), f(true))", fail);
	("let f = fun x y -> let a = eq(x, y) in eq(x, y) in f", OK "forall[a] (a, a) -> bool");
	("let f = fun x y -> let a = eq_curry(x)(y) in eq_curry(x)(y) in f",
		OK "forall[a] (a, a) -> bool");
	("id(id)", OK "forall[a] a -> a");
	("choose(fun x y -> x, fun x y -> y)", OK "forall[a] (a, a) -> a");
	("choose_curry(fun x y -> x)(fun x y -> y)", OK "forall[a] (a, a) -> a");
	("let x = id in let y = let z = x(id) in z in y", OK "forall[a] a -> a");
	("single(id)", OK "forall[a] list[a -> a]");
	("cons_curry(id)(nil)", OK "forall[a] list[a -> a]");
	("let lst1 = cons(id, nil) in let lst2 = cons(succ, lst1) in lst2", OK "list[int -> int]");
	("cons_curry(id)(cons_curry(succ)(cons_curry(id)(nil)))", OK "list[int -> int]");
	("plus(one, true)", error "cannot unify types int and bool");
	("plus(one)", error "unexpected number of arguments");
	("fun x -> let y = x in y", OK "forall[a] a -> a");
	("fun x -> let y = let z = x(fun x -> x) in z in y", OK "forall[a b] ((a -> a) -> b) -> b");
	("fun x -> fun y -> let x = x(y) in x(y)", OK "forall[a b] (a -> a -> b) -> a -> b");
	("fun x -> let y = fun z -> x(z) in y", OK "forall[a b] (a -> b) -> a -> b");
	("fun x -> let y = fun z -> x in y", OK "forall[a b] a -> b -> a");
	("fun x -> fun y -> let x = x(y) in fun x -> y(x)",
		OK "forall[a b c] ((a -> b) -> c) -> (a -> b) -> a -> b");
	("fun x -> let y = x in y(y)", error "recursive types");
	("fun x -> let y = fun z -> z in y(y)", OK "forall[a b] a -> b -> b");
	("fun x -> x(x)", error "recursive types");
	("one(id)", error "expected a function");
	("fun f -> let x = fun g y -> let _ = g(y) in eq(f, g) in x",
		OK "forall[a b] (a -> b) -> (a -> b, a) -> bool");
	("let const = fun x -> fun y -> x in const", OK "forall[a b] a -> b -> a");
	("let apply = fun f x -> f(x) in apply", OK "forall[a b] (a -> b, a) -> b");
	("let apply_curry = fun f -> fun x -> f(x) in apply_curry", OK "forall[a b] (a -> b) -> a -> b");

	(* HMF *)
	("ids", OK "list[forall[a] a -> a]");
	("fun f -> pair(f(one), f(true))", fail);
	("fun (f : forall[a] a -> a) -> pair(f(one), f(true))",
		OK "(forall[a] a -> a) -> pair[int, bool]");
	("cons(ids, nil)", OK "list[list[forall[a] a -> a]]");
	("choose(nil, ids)", OK "list[forall[a] a -> a]");
	("choose(ids, nil)", OK "list[forall[a] a -> a]");
	("cons(fun x -> x, ids)", OK "list[forall[a] a -> a]");
	("let rev_cons = fun x y -> cons(y, x) in rev_cons(ids, id)", OK "list[forall[a] a -> a]");
	("cons(id, ids)", OK "list[forall[a] a -> a]");
	("cons(id, cons(succ, nil))", OK "list[int -> int]");
	("poly(id)", OK "pair[int, bool]");
	("poly(fun x -> x)", OK "pair[int, bool]");
	("poly(succ)", fail);
	("apply(succ, one)", OK "int");
	("rev_apply(one, succ)", OK "int");
	("apply(poly, id)", OK "pair[int, bool]");
	("apply_curry(poly)(id)", OK "pair[int, bool]");
	("rev_apply(id, poly)", OK "pair[int, bool]");
	("rev_apply_curry(id)(poly)", fail);
	("(id : forall[a] a -> a) : int -> int", OK "int -> int");
	("single(id : forall[a] a -> a)", OK "list[forall[a] a -> a]");
	("(fun x -> fun y -> let z = choose(x, y) in z)(id : forall[a] a -> a)",
		OK "(forall[a] a -> a) -> (forall[a] a -> a)");
	("fun (x : forall[a] a -> a) -> x", OK "forall[a] (forall[b] b -> b) -> a -> a");
	("id_id(id)", OK "forall[a] a -> a");
	("almost_id_id(id)", OK "forall[a] a -> a");
	("fun id -> poly(id)", fail);
	("fun ids -> id_ids(ids)", fail);
	("poly(id(id))", OK "pair[int, bool]");
	("length(ids)", OK "int");
	("map(head, single(ids))", OK "list[forall[a] a -> a]");
	("map_curry(head)(single(ids))", OK "list[forall[a] a -> a]");
	("apply(map_curry(head), single(ids))", OK "list[forall[a] a -> a]");
	("apply_curry(map_curry(head))(single(ids))", OK "list[forall[a] a -> a]");
	("apply(id, one)", OK "int");
	("apply_curry(id)(one)", OK "int");
	("poly(magic)", OK "pair[int, bool]");
	("id_magic(magic)", OK "forall[a b] a -> b");
	("fun (f : forall[a b] a -> b) -> let a = id_magic(f) in one", OK "(forall[a b] a -> b) -> int");
	("fun (f : some[a b] a -> b) -> id_magic(f)", fail);
	("id_magic(id)", fail);
	("fun (f : forall[a b] a -> b) -> f : forall[a] a -> a",
		OK "(forall[a b] a -> b) -> (forall[a] a -> a)");
	("let const = (any : forall[a] a -> (forall[b] b -> a)) in const(any)", OK "forall[a b] a -> b");

	(* propagation of types *)
	("single(id) : list[forall[a] a -> a]", OK "list[forall[a] a -> a]");
	("id(single(id)) : list[forall[a] a -> a]", fail);
	("cons(single(id), single(ids))", OK "list[list[forall[a] a -> a]]");
	("id_id(id) : int -> int", OK "int -> int");
	("head(ids)(one) : int", OK "int");
	("head(ids) : int -> int", OK "int -> int");
	("let f = head(ids) in f : int -> int", OK "int -> int");
	("cons(single(id) : list[forall[a] a -> a], single(single(fun x -> x)))",
		OK "list[list[forall[a] a -> a]]");
	("id_succ(head(map(id, ids)))", OK "int -> int");
	("(fun f -> f(f)) : (forall[a] a -> a) -> (forall[a] a -> a)",
		OK "(forall[a] a -> a) -> (forall[a] a -> a)");
	("(fun f -> f(f)) : forall[b] (forall[a] a -> a) -> b -> b",
		OK "forall[a] (forall[b] b -> b) -> a -> a");
	("(let x = one in (fun f -> pair(f(x), f(true)))) : (forall[a] a -> a) -> pair[int, bool]",
		OK "(forall[a] a -> a) -> pair[int, bool]");
	("let returnST = any : forall[a s] a -> ST[s, a] in " ^
	 "returnST(one) : forall[s] ST[s, int]", OK "forall[s] ST[s, int]");
	("special(fun f -> f(f))", OK "forall[a] a -> a");
	("apply(special, fun f -> f(f))", OK "forall[a] a -> a");
	("rev_apply(fun f -> f(f), special)", OK "forall[a] a -> a");
	("apply(fun f -> choose(id_id, f), id_id : (forall[a] a -> a) -> (forall[a] a -> a))",
		OK "(forall[a] a -> a) -> (forall[a] a -> a)");
	("rev_apply(id_id : (forall[a] a -> a) -> (forall[a] a -> a), fun f -> choose(id_id, f))",
		OK "(forall[a] a -> a) -> (forall[a] a -> a)");
	]



let string_of_result = function
	| Fail None -> "Fail"
	| Fail (Some msg) -> "Fail " ^ msg
	| OK ty_str -> "OK " ^ ty_str

let cmp_result result1 result2 = match (result1, result2) with
	| Fail None, Fail _ | Fail _, Fail None -> true
	| Fail (Some msg1), Fail (Some msg2) -> msg1 = msg2
	| OK ty_str1, OK ty_str2 -> ty_str1 = ty_str2
	| _ -> false

let make_single_test_case (code, expected_result) =
	let expected_result = match expected_result with
		| OK ty_str -> OK (string_of_ty (Parser.ty_eof Lexer.token (Lexing.from_string ty_str)))
		| x -> x
	in
	String.escaped code >:: fun _ ->
		Infer.reset_id () ;
		let result =
			try
				let ty =
					Propagate.infer Core.core 0 None Propagate.Generalized
						(Parser.expr_eof Lexer.token (Lexing.from_string code))
				in
				OK (string_of_ty ty)
			with Infer.Error msg ->
				Fail (Some msg)
		in
		assert_equal ~printer:string_of_result ~cmp:cmp_result expected_result result

let suite =
	"test_propagate" >::: List.map make_single_test_case test_cases




