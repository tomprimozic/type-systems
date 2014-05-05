open OUnit2
open Expr

type result =
	| OK
	| Fail of string option

let fail = Fail None
let error msg = Fail (Some msg)

let test_cases = [
		("1 : int if true", OK);
		("1 : int if false", fail);
		("1 : int if 1 > 2", fail);
		("1 : int if 1 + 5 > 2", OK);
		("1 : int if 1 != 0 and - 2 <= 2 - 1", OK);
		("let x = 1 in 1 : int if x > 2", fail);
		("let x = 1 in 1 : int if x + 3 > 2", OK);
		("1 / 0", fail);
		("let x = 0 in 1 / x", fail);
		("1 / 1", OK);
		("let x = 1 in 1 / x", OK);
		("1 / succ(0)", OK);
		("random1toN(-1)", fail);
		("1 / random1toN(5)", OK);
		("if 2 > 1 then 1 else 1 / 0", OK);
		("let x = random1toN(10) in if x > 5 then 1 / (x - 5) else 1 / (6 - x)", OK);
		("let x = random1toN(1000) in " ^
		 " let z = " ^
		 "  if x > 10 then " ^
		 "   let n = random1toN(x) in " ^
		 "   n - 2 * x " ^
		 "  else " ^
		 "   let m = random1toN(10) + 10 in " ^
		 "   m - x " ^
		 " in " ^
		 " 1 / z", OK);
		("let x = random1toN(100) in let y = random1toN(100) in " ^
		 "if x > 0 then " ^
		 " if y > 0 then " ^
		 "  1 / x + 1 / y " ^
		 " else " ^
		 "  1 / x + y " ^
		 "else " ^
		 " x + y", OK);
		("fun (x : int) -> 1 / x", fail);
		("fun (x : int if x > 0) -> 1 / x", OK);
	]



let string_of_result = function
	| Fail None -> "Fail"
	| Fail (Some msg) -> "Fail " ^ msg
	| OK -> "OK"

let cmp_result result1 result2 = match (result1, result2) with
	| Fail None, Fail _ | Fail _, Fail None -> true
	| Fail (Some msg1), Fail (Some msg2) -> msg1 = msg2
	| OK, OK -> true
	| _ -> false

let make_single_test_case (code, expected_result) =
	String.escaped code >:: fun _ ->
		let result =
			try
				let expr = Parser.expr_eof Lexer.token (Lexing.from_string code) in
				let t_expr = Infer.infer Core.plain_env 0 expr in
				Refined.prove t_expr ;
				OK
			with Refined.Error msg ->
				Fail (Some msg)
		in
		assert_equal ~printer:string_of_result ~cmp:cmp_result expected_result result

let suite =
	"test_prove" >::: List.map make_single_test_case test_cases



