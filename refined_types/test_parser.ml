open OUnit2
open Expr

type result =
	| OK of s_expr
	| Fail

let bound i = TVar (ref (Generic i))

let test_cases = [
	("", Fail);
	("a", OK (SVar "a"));
	("f(x, 1, true)", OK (SCall(SVar "f", [SVar "x"; SInt 1; SBool true])));
	("f(x)(false)", OK (SCall(SCall(SVar "f", [SVar "x"]), [SBool false])));
	("let f = fun(x, y : int) -> g(x > -2, y + 1) in f(a, b)",
		OK (SLet("f", SFun([("x", None); ("y", Some (TConst "int", None))], None,
			SCall(SVar "g", [SCall(SVar ">", [SVar "x"; SCall(SVar "unary-", [SInt 2])]); 
			SCall(SVar "+", [SVar "y"; SInt 1])])), SCall(SVar "f", [SVar "a"; SVar "b"]))));
	("let x = a : array[byte] in let y = b : int if b > 0 in f(x, y)",
		OK (SLet("x", SCast(SVar "a", TApp("array", [TConst "byte"]), None),
			SLet("y", SCast(SVar "b", TConst "int", Some (SCall(SVar ">", [SVar "b"; SInt 0]))),
			SCall(SVar "f", [SVar "x"; SVar "y"])))));
	("a : int", OK (SCast(SVar "a", TConst "int", None)));
	("a : int if a > 0",
		OK (SCast(SVar "a", TConst "int", Some (SCall(SVar ">", [SVar "a"; SInt 0])))));
	("1 : int if a > 0",
		OK (SCast(SInt 1, TConst "int", Some (SCall(SVar ">", [SVar "a"; SInt 0])))));
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
	("fun() : int -> y", OK (SFun([], Some (TConst "int", None), SVar "y")));
	("1 : int", OK (SCast(SInt 1, TConst "int", None)));
	("1 : some[a] a", OK (SCast(SInt 1, bound 0, None)));
	("1 : some[a] array[a]", OK (SCast(SInt 1, TApp("array", [bound 0]), None)));
	("1 : some[a b] pair[a, pair[b, array[a]]]",
		OK (SCast(SInt 1, TApp("pair", [bound 0; TApp("pair",
			[bound 1; TApp("array", [bound 0])])]), None)));
	("id : some[a] a -> a", OK (SCast(SVar "id", (TArrow([(bound 0, None)], (bound 0, None))), None)));
	("fun(x : some[a] a, y : int -> int, z : (int -> int) if z(0) != 1) : some[a] array[a] -> 1",
		OK (SFun([("x", Some (bound 0, None)); ("y", Some (TArrow([(TConst "int", None)],
			(TConst "int", None)), None)); ("z", Some (TArrow([(TConst "int", None)],
			(TConst "int", None)), Some (SCall(SVar "!=", [SCall(SVar "z", [SInt 0]); SInt 1]))))],
			Some (TApp("array", [bound 1]), None), SInt 1)));
	("fun(f : (x : int if x != 0) -> (y : int if x != y)) -> f(0)",
		OK (SFun([("f", Some (TArrow([(TConst "int", Some ("x", Some (SCall(SVar "!=",
			[SVar "x"; SInt 0]))))], (TConst "int", Some ("y", Some (SCall(SVar "!=",
			[SVar "x"; SVar "y"]))))), None))], None, SCall(SVar "f", [SInt 0]))));
	("b : some[a] array[a] if length(b) > 0",
		OK (SCast(SVar "b", TApp("array", [bound 0]), Some (SCall(SVar ">", [SCall(SVar
			"length", [SVar "b"]); SInt 0])))));
	("plus : (x : int, y : int) -> (z : int if z == x + y)",
		OK (SCast(SVar "plus", TArrow([(TConst "int", Some ("x", None)); (TConst "int",
			Some ("y", None))], (TConst "int", Some ("z", Some (SCall(SVar "==",
			[SVar "z"; SCall(SVar "+", [SVar "x"; SVar "y"])]))))), None)));
	("f : (x : int if x > 0) -> ((y : int) -> (z : int if z == x + y))",
		OK (SCast(SVar "f", TArrow([(TConst "int", Some ("x", Some (SCall(SVar ">", [SVar "x";
			SInt 0]))))], (TArrow([(TConst "int", Some ("y", None))], (TConst "int", Some ("z",
			Some (SCall(SVar "==", [SVar "z"; SCall(SVar "+", [SVar "x"; SVar "y"])]))))), None)), None)));
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
(*
		assert_equal ~printer:string_of_result expected_result result
*)
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


