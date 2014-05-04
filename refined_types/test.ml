open OUnit2

let suite = test_list [Test_lexer.suite; Test_parser.suite; Test_infer.suite]

let () = run_test_tt_main suite

