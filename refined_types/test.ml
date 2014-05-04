open OUnit2

let suite = test_list [Test_lexer.suite; Test_parser.suite; Test_infer.suite; Test_refined.suite]

let () = run_test_tt_main suite

