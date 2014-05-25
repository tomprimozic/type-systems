open Expr
open Infer

	let builtins = [
			("not", "bool -> bool");
			("and", "(bool, bool) -> bool");
			("or", "(bool, bool) -> bool");

			("==", "forall[a] (a, a) -> bool");
			("!=", "forall[a] (a, a) -> bool");

			("<", "(int, int) -> bool");
			(">", "(int, int) -> bool");
			("<=", "(int, int) -> bool");
			(">=", "(int, int) -> bool");

			("+", "(int, int) -> int");
			("-", "(int, int) -> int");
			("*", "(int, int) -> int");
			("/", "(int, i : int if i != 0) -> int");
			("%", "(int, i : int if i != 0) -> int");
			("unary-", "int -> int");
		]

	let uninterpreted = [
			("length", "forall[t] (a : array[t]) -> (l : int if l >= 0)");
			("is_prime", "(i : int if i >= 1) -> bool");
		]

	let primitives = [
			("get", "forall[t] (a : array[t], i : int if i >= 0 and i < length(a)) -> t");
			("alloc", "forall[t] (i : int) -> (a : array[t] if length(a) == i)");
			("memcpy", "(dst : array[byte], src : array[byte],
			           num : int if num <= length(dst) and num <= length(src)) -> unit");
			("head", "forall[t] (a : array[t] if length(a) > 0) -> t");
			("is_empty", "forall[t] (a : array[t]) -> (b : bool if b == (length(a) == 0))");
			("head1", "forall[t] (a : array[t] if not is_empty(a)) -> t");
			("fac", "(i : int if i >= 0) -> (j : int if j > 0 and j >= i)");
			("succ", "(i : int) -> (j : int if j == i + 1)");
			("square", "(i : int) -> (j : int if j == i * i)");
			("random1toN", "(N : int if N >= 1) -> (i : int if 1 <= i and i <= N)");
			("my_not", "(b : bool) -> (c : bool if c == (not b))");

			("make_const", "forall[a b] (x : a) -> b -> (y : a if y == x)");

			("pair", "forall[t s] (t, s) -> pair[t, s]");
			("first", "forall[t s] pair[t, s] -> t");
			("second", "forall[t s] pair[t, s] -> s");

			("cons", "forall[a] (a, list[a]) -> list[a]");
			("cons_curry", "forall[a] a -> list[a] -> list[a]");
			("nil", "forall[a] list[a]");

			("id", "forall[a] a -> a");
			("choose", "forall[a] (x : a, y : a) -> (z : a if z == x or z == y)");
			("plain_choose", "forall[a] (a, a) -> a");
			("choose_curry", "forall[a] (x : a) -> (y : a) -> (z : a if z == x or z == y)");
			("plain_choose_curry", "forall[a] a -> a -> a");
		]


let env =
	let f env (var_name, ty_str) =
		let ty = Parser.ty_forall_eof Lexer.token (Lexing.from_string ty_str) in
		let t_ty = infer_ty env 0 ty in
		Env.extend var_name t_ty env
	in
	List.fold_left f Env.empty (List.flatten [builtins; uninterpreted; primitives])

let plain_env = Env.map strip_refined_types env
