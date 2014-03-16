open OUnit2
open Expr

type result =
	| OK of expr
	| Fail

let bound i = TVar (ref (Bound i))

let test_cases = [
	("", Fail);
	("a", OK (Var "a"));
	("f(x, y)", OK (Call(Var "f", [Var "x"; Var "y"])));
	("f(x)(y)", OK (Call(Call(Var "f", [Var "x"]), [Var "y"])));
	("let f = fun x y -> g(x, y) in f(a, b)",
		OK (Let("f", None, Fun([("x", None); ("y", None)], Call(Var "g", [Var "x"; Var "y"])),
			Call(Var "f", [Var "a"; Var "b"]))));
	("let x = a in " ^
	 "let y = b in " ^
	 "f(x, y)", OK (Let("x", None, Var "a", Let("y", None, Var "b", Call(Var "f", [Var "x"; Var "y"])))));
	("f x", Fail);
	("let a = one", Fail);
	("a, b", Fail);
	("a = b", Fail);
	("()", Fail);
	("fun x, y -> y", Fail);
	("fun -> y", OK (Fun([], Var "y")));
	("id : some[a] a -> a", OK (Ann(Var "id", (TArrow([bound 0], bound 0)))));
	("fun (x : some[a] a) (y : ?) (z : int) -> y",
		OK (Fun([("x", Some (bound 0)); ("y", Some TDynamic);
			("z", Some(TConst "int"))], Var "y")));
	("fun (x : _) (y : ?) (z : int) -> y",
		OK (Fun([("x", Some (bound 0)); ("y", Some TDynamic);
			("z", Some(TConst "int"))], Var "y")));
	("let x : some[a] a = one in x", OK (Let("x", Some(bound 0), Var "one", Var "x")));
	("let x : _ = one in x", OK (Let("x", Some(bound 0), Var "one", Var "x")));
	("let x : ? = one in x", OK (Let("x", Some(TDynamic), Var "one", Var "x")));
	]



let string_of_result = function
	| Fail -> "Fail"
	| OK expr -> "OK (" ^ string_of_expr expr ^ ")"

let make_single_test_case (code, expected_result) =
	String.escaped code >:: fun _ ->
		Infer.reset_id () ;
		let result =
			try
				OK (Parser.expr_eof Lexer.token (Lexing.from_string code))
			with Parsing.Parse_error ->
				Fail
		in
		assert_equal ~printer:string_of_result expected_result result

let suite =
	"test_parser" >::: List.map make_single_test_case test_cases


