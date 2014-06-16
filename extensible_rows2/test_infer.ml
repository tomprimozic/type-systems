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
	("fun x -> x", OK "forall[int] int -> int");
	("pair", OK "forall[a b] (a, b) -> pair[a, b]") ;
	("pair", OK "forall[z x] (x, z) -> pair[x, z]") ;
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
	("cons(id, nil)", OK "forall[a] list[a -> a]");
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
	("let fib1 = fun fib -> fun n -> " ^
	 "if(eq(n, one), one, " ^
	 "if(eq(n, zero), one, " ^
	 "plus(fib(minus(n, one)), fib(minus(n, succ(one)))))) in " ^
	 "fix(fib1)", OK "int -> int");

	(* records *)
	("{}", OK "{}");
	("{}.x", fail);
	("{a = one}", OK "{a : int}");
	("{a = one, b = true}", OK "{a : int, b : bool}");
	("{b = true, a = one}", OK "{b : bool, a : int}");
	("{a = one, b = true}.a", OK "int");
	("{a = one, b = true}.b", OK "bool");
	("{a = one, b = true}.c", error "row does not contain label c");
	("{f = fun x -> x}", OK "forall[a] {f : a -> a}");
	("let r = {a = id, b = succ} in choose(r.a, r.b)", OK "int -> int");
	("let r = {a = id, b = fun x -> x} in choose(r.a, r.b)", OK "forall[a] a -> a");
	("choose({a = one}, {})", fail);
	("{ x = zero | { y = one | {} } }", OK "{x : int, y : int}");
	("choose({ x = zero | { y = one | {} } }, {x = one, y = zero})", OK "{x : int, y : int}");
	("{{} - x}", fail);
	("{{x = one, y = zero} - x}", OK "{y : int}");
	("{ x = true | {x = one}}", OK "{x : bool, x : int}");
	("let a = {} in {b = one | a}", OK "{b : int}");
	("let a = {x = one} in {x = true | a}.x", OK "bool");
	("let a = {x = one} in a.y", error "row does not contain label y");
	("let a = {x = one} in {a - x}", OK "{}");
	("let a = {x = one} in let b = {x = true | a} in {b - x}.x", OK "int");
	("fun r -> {x = one | r}", OK "forall[r] {r} -> {x : int | r}");
	("fun r -> r.x", OK "forall[r a] {x : a | r} -> a");
	("let get_x = fun r -> r.x in get_x({y = one, x = zero})", OK "int");
	("let get_x = fun r -> r.x in get_x({y = one, z = true})", error "row does not contain label x");
	("fun r -> choose({x = zero | r}, {x = one | {}})", OK "{} -> {x : int}");
	("fun r -> choose({x = zero | r}, {x = one})", OK "{} -> {x : int}");
	("fun r -> choose({x = zero | r}, {x = one | r})", OK "forall[r] {r} -> {x : int | r}");
	("fun r -> choose({x = zero | r}, {y = one | r})", error "recursive row types");
	("let f = fun x -> x.t(one) in f({t = succ})", OK "int");
	("let f = fun x -> x.t(one) in f({t = id})", OK "int");
	("{x = one, x = true}", OK "{x : int, x : bool}");

	("let f = fun r -> let y = r.y in choose(r, {x = one, x = true}) in f",
		error "row does not contain label y");
	("fun r -> let y = choose(r.x, one) in let z = choose({r - x}.x, true) in r",
		OK "forall[a r] {x : int, x : bool | r} -> {x : int, x : bool | r}");
	("fun r -> choose({x = zero | r}, {x = one, x = true})", OK "{x : bool} -> {x : int, x : bool}");
	("fun r -> choose(r, {x = one, x = true})", OK "{x : int, x : bool} -> {x : int, x : bool}");
	("fun r -> choose({x = zero | r}, {x = true | r})", error "cannot unify types int and bool");
	("fun r s -> " ^
	 "choose({b = true, a = one, c = zero, b = half | r}, {b = false, c = one, d = half | s})",
		OK ("forall[a] ({d : float | a}, {a : int, b : float | a}) -> " ^
		    "{a : int, b : bool, b : float, c : int, d : float | a}"));
	("fun r s -> choose({b = true, a = one, c = zero, b = half | r}, {b = false, c = one | s})",
		OK "forall[a] ({a}, {a : int, b : float | a}) -> {a : int, b : bool, b : float, c : int | a}");
	("fun r s -> choose({b = true, c = zero | r}, {b = false, c = one, d = half | s})",
		OK "forall[a] ({d : float | a}, {a}) -> {b : bool, c : int, d : float | a}");
	("fun r s -> " ^
	 "choose({b = true, a = one, c = one, b = half | r}, {b = false, c = one, a = one, b = half | s})",
		OK "forall[a] ({a}, {a}) -> {a : int, b : bool, b : float, c : int | a}");
	("fun r -> {x = r | r}", OK "forall[a] {a} -> {x : {a} | a}");

	(* variants *)
	(":X one", OK "forall[a] [X : int | a]");
	("choose(choose(:x one, :Y true), choose(:X half, :y nil))",
		OK "forall[a b] [X : float, Y : bool, x : int, y : list[a] | b]");
	("choose(:X one, :X true)", error "cannot unify types int and bool");
	("choose(:X {x = one, y = false}, :Y {w = half})",
		OK "forall[a] [X : {x : int, y : bool}, Y : {w : float} | a]");
	("let e = choose(choose(:x one, :Y true), choose(:X half, :y nil)) in " ^
	 "match e { :x i -> i | :Y y -> zero}", error "row does not contain label X");
	("fun x y -> match x {:a i -> one | :b i -> zero | :c i -> y}",
		OK "forall [a b c] ([a : a, b : b, c : c], int) -> int");
	("fun a -> match a {:X i -> i | r -> one}", OK "forall[a] [X : int | a] -> int");
	("let f = fun m -> match m {:y a -> one | :Y b -> zero | :z z -> zero} in " ^
	 "fun e -> match e { :x i -> i | :X f -> one | r -> f(r)}",
	 OK "forall[a b c d] [X : a, Y : b, x : int, y : c, z : d] -> int");
	("let e = choose(choose(:x one, :Y true), choose(:X half, :y nil)) in " ^
	 "let f = fun m -> match m {:y a -> one | :Y b -> zero | :z z -> zero} in " ^
	 "match e { :x i -> i | :X f -> one | r -> f(r)}", OK "int");
	("fun e -> match e {:X a -> one | :X i -> i}", OK "forall[a] [X : a, X : int] -> int");
	("let f = fun g -> fun e -> match e { :x i -> i | :Y a -> one | r -> g(r)} in " ^
	 "let g = fun s -> match s {:x j -> head(j) | :X a -> zero} in " ^
	 "f(g)", OK "forall[a b] [X : a, Y : b, x : int, x : list[int]] -> int");
	("fun e -> match e { :X a -> plus(a.x, one) }", OK "forall[a] [X : {x : int | a}] -> int");
	("let count1 = fun count -> fun x -> " ^
	 " match x {:Cons a -> plus(one, count(a.tail)) | :Nil _ -> zero} in " ^
	 "fix(count1)", error "recursive types");
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
				let ty = Infer.infer Core.core 0 (Parser.expr_eof Lexer.token (Lexing.from_string code)) in
				let generalized_ty = Infer.generalize (-1) ty in
				OK (string_of_ty generalized_ty)
			with Infer.Error msg ->
				Fail (Some msg)
		in
		assert_equal ~printer:string_of_result ~cmp:cmp_result expected_result result

let suite =
	"test_infer" >::: List.map make_single_test_case test_cases



