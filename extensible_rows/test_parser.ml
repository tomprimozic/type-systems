open OUnit2
open Expr

type result =
	| OK of expr
	| Fail


let test_cases = [
	("", Fail);
	("a", OK (Var "a"));
	("f(x, y)", OK (Call(Var "f", [Var "x"; Var "y"])));
	("f(x)(y)", OK (Call(Call(Var "f", [Var "x"]), [Var "y"])));
	("let f = fun x y -> g(x, y) in f(a, b)",
		OK (Let("f", Fun(["x"; "y"], Call(Var "g", [Var "x"; Var "y"])),
			Call(Var "f", [Var "a"; Var "b"]))));
	("let x = a in " ^
	 "let y = b in " ^
	 "f(x, y)", OK (Let("x", Var "a", Let("y", Var "b", Call(Var "f", [Var "x"; Var "y"])))));
	("f x", Fail);
	("let a = one", Fail);
	("a, b", Fail);
	("a = b", Fail);
	("()", Fail);
	("fun x, y -> y", Fail);

	(* records *)
	("{}", OK RecordEmpty);
	("{ }", OK RecordEmpty);
	("{", Fail);
	("a.x", OK (RecordSelect(Var "a", "x")));
	("{m - a}", OK (RecordRestrict(Var "m", "a")));
	("{m - a", Fail);
	("m - a", Fail);
	("{a = x}", OK (RecordExtend("a", Var "x", RecordEmpty)));
	("{a = x", Fail);
	("{a=x, b = y}", OK (RecordExtend("a", Var "x", RecordExtend("b", Var "y", RecordEmpty))));
	("{b = y ,a=x}", OK (RecordExtend("b", Var "y", RecordExtend("a", Var "x", RecordEmpty))));
	("{a=x,h=w,d=y,b=q,g=z,c=t,e=s,f=r}",
		OK (RecordExtend("a", Var "x", RecordExtend("h", Var "w", RecordExtend("d", Var "y",
		RecordExtend("b", Var "q", RecordExtend("g", Var "z", RecordExtend("c", Var "t",
    RecordExtend("e", Var "s", RecordExtend("f", Var "r", RecordEmpty))))))))));
	("{a = x|m}", OK (RecordExtend ("a", Var "x", Var "m")));
	("{a | m}", Fail);
	("{ a = x, b = y | m}", OK (RecordExtend("a", Var "x", RecordExtend("b", Var "y", Var "m"))));
	("{ a = x, b = y | {m - a} }",
		OK (RecordExtend("a", Var "x", RecordExtend("b", Var "y", RecordRestrict(Var "m", "a")))));
	("{ b = y | m - a }", Fail);
	("let x = {a = f(x), b = y.b} in { a = fun z -> z | {x - a} }",
		OK (Let("x", RecordExtend("a", Call(Var "f", [Var "x"]), RecordExtend("b",
		RecordSelect(Var "y", "b"), RecordEmpty)), RecordExtend("a", Fun(["z"], Var "z"),
		RecordRestrict(Var "x", "a")))));
	]



let string_of_result = function
	| Fail -> "Fail"
	| OK expr -> "OK (" ^ string_of_expr expr ^ ")"

let make_single_test_case (code, expected_result) =
	String.escaped code >:: fun _ ->
		let result =
			try
				OK (Parser.expr_eof Lexer.token (Lexing.from_string code))
			with Parsing.Parse_error ->
				Fail
		in
		assert_equal ~printer:string_of_result expected_result result

let suite =
	"test_parser" >::: List.map make_single_test_case test_cases


