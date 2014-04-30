open OUnit2
open Expr

type result =
	| OK of s_expr
	| Fail

let bound i = STVar (ref (SGeneric i))

let test_cases = [
	("", Fail);
	("a", OK (SVar "a"));
	("f(x, 1, true)", OK (SCall(SVar "f", [SVar "x"; SInt 1; SBool true])));
	("f(x)(false)", OK (SCall(SCall(SVar "f", [SVar "x"]), [SBool false])));
	("let f = fun(x, y : int) -> g(x > -2, y + 1) in f(a, b)",
		OK (SLet("f", SFun([("x", None); ("y", Some (STConst "int"))], None,
			SCall(SVar "g", [SCall(SVar ">", [SVar "x"; SCall(SVar "unary-", [SInt 2])]); 
			SCall(SVar "+", [SVar "y"; SInt 1])])), SCall(SVar "f", [SVar "a"; SVar "b"]))));
	("let x = a : array[byte] in let y = b : int if b > 0 in f(x, y)",
		OK (SLet("x", SCast(SVar "a", STApp("array", [STConst "byte"])),
			SLet("y", SCast(SVar "b", STRefined("b", STConst "int",
			SCall(SVar ">", [SVar "b"; SInt 0]))), SCall(SVar "f", [SVar "x"; SVar "y"])))));
	("a : int", OK (SCast(SVar "a", STConst "int")));
	("a : int if a > 0",
		OK (SCast(SVar "a", STRefined("a", STConst "int", SCall(SVar ">", [SVar "a"; SInt 0])))));
	("1 : int if a > 0",
		OK (SCast(SInt 1, STRefined("", STConst "int", SCall(SVar ">", [SVar "a"; SInt 0])))));
	("f x", Fail);
	("f x", Fail);
	("let a = one", Fail);
	("a, b", Fail);
	("a = b", Fail);
	("()", Fail);
	("fun x, y -> y", Fail);
	("fun x y -> y", Fail);
	("a and b or c", Fail);
	("(a and b) or c", OK (SCall(SVar "or", [SCall(SVar "and", [SVar "a"; SVar "b"]); SVar "c"])));
	("not a or b", Fail);
	("(not a > 0) or b",
	OK (SCall(SVar "or", [SCall(SVar "not", [SCall(SVar ">", [SVar "a"; SInt 0])]); SVar "b"])));
	("fun() : int -> y", OK (SFun([], Some (STConst "int"), SVar "y")));
	("1 : int", OK (SCast(SInt 1, STConst "int")));
	("1 : some[a] a", OK (SCast(SInt 1, bound 0)));
	("1 : some[a] array[a]", OK (SCast(SInt 1, STApp("array", [bound 0]))));
	("1 : some[a b] pair[a, pair[b, array[a]]]",
		OK (SCast(SInt 1, STApp("pair", [bound 0; STApp("pair",
			[bound 1; STApp("array", [bound 0])])]))));
	("id : some[a] a -> a", OK (SCast(SVar "id", (STArrow([bound 0], bound 0)))));
	("fun(x : some[a] a, y : int -> int, z : (int -> int) if z(0) != 1) : some[a] array[a] -> 1",
		OK (SFun([("x", Some (bound 0)); ("y", Some (STArrow([STConst "int"], STConst "int")));
			("z", Some (STRefined("z", STArrow([STConst "int"], STConst "int"),
			SCall(SVar "!=", [SCall(SVar "z", [SInt 0]); SInt 1]))))],
			Some (STApp("array", [bound 1])), SInt 1)));
	("fun(f : (x : int if x != 0) -> (y : int if x != y)) -> f(0)",
		OK (SFun([("f", Some (STArrow([STRefined("x", STConst "int", SCall(SVar "!=",
			[SVar "x"; SInt 0]))], STRefined("y", STConst "int", SCall(SVar "!=",
			[SVar "x"; SVar "y"])))))], None, SCall(SVar "f", [SInt 0]))));
	("1 : some[a] pair[x : int if x > 0, array[a]]",
		OK (SCast(SInt 1, STApp("pair", [STRefined("x", STConst "int", SCall(SVar ">",
			[SVar "x"; SInt 0])); STApp("array", [bound 0])]))));
	("b : some[a] (b : array[a] if length(b) > 0)",
		OK (SCast(SVar "b", STRefined("b", STApp("array", [bound 0]), SCall(SVar ">", [SCall(SVar "length", [SVar "b"]); SInt 0])))));
	("plus : (x : int, y : int) -> (z : int if z == x + y)",
		OK (SCast(SVar "plus", STArrow([STRefined("x", STConst "int", SBool true);
			STRefined("y", STConst "int", SBool true)], STRefined("z", STConst "int",
			SCall(SVar "==", [SVar "z"; SCall(SVar "+", [SVar "x"; SVar "y"])]))))));
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
		assert_equal ~printer:string_of_result expected_result result ;
		match result with
			| OK expr -> begin
					let expr_str = string_of_expr expr in
(*					assert_equal ~printer:(fun x -> x) code expr_str ; *)
					Infer.reset_id() ;
					try
						let new_result = OK (Parser.expr_eof Lexer.token (Lexing.from_string expr_str)) in
						assert_equal ~printer:string_of_result ~msg:"string_of_expr error"
							expected_result new_result
					with Parsing.Parse_error ->
						assert_failure ("string_of_expr parsing error: " ^ expr_str)
				end
			| Fail -> ()

let suite =
	"test_parser" >::: List.map make_single_test_case test_cases


