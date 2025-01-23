use crate::{codegen, parser::parse, vm};

#[test]
fn test_examples() {
    let _ = parse(include_str!("../examples/fizzbuzz.pty")).unwrap();
    let _ = parse(include_str!("../examples/lexer.pty")).unwrap();
}

macro_rules! test_expr {
    ($expr: literal, $expected: literal) => {
        let ast = parse(concat!($expr, ";")).unwrap();
        let bytecode = codegen::codegen(&ast);
        let mut output = vec![];
        vm::execute_bytecode_with(&mut output, &bytecode).unwrap();
        assert_eq!(String::from_utf8(output).unwrap().trim(), $expected);
    };
}

#[test]
fn test_obvious() {
    test_expr!("println(1 + 2)", "3");
    test_expr!("for i in 0..=5 { println(i); }", "0\n1\n2\n3\n4\n5");
    test_expr!("for i in 0..=5 { if i == 0 { continue; } println(i); }", "1\n2\n3\n4\n5");
    test_expr!("for i in 0..=5 { if i == 4 { break; } println(i); }", "0\n1\n2\n3");
    test_expr!(
        "let i = 0; while true { if i == 4 { break; } println(i); i = i + 1; }",
        "0\n1\n2\n3"
    );
    test_expr!("println(A { str: 1 })", "{ str: 1 }");
    test_expr!("println((A { name: \"Bob\" }).name)", "Bob");
    test_expr!("println(1 < 2)", "true");
    test_expr!("println(5 > 4)", "true");
    test_expr!("println(str_len(\"123456789\"))", "9");
    test_expr!("let i = 5; println(i < str_len(\"123456789\"))", "true");
    test_expr!("println(false && false)", "false");
    test_expr!("println(false && true)", "false");
    test_expr!("println(true && false)", "false");
    test_expr!("println(true && true)", "true");
    test_expr!("println(false || false)", "false");
    test_expr!("println(false || true)", "true");
    test_expr!("println(true || false)", "true");
    test_expr!("println(true || true)", "true");
    test_expr!("let lexer = Lexer { len: 10 }; println(lexer.len);", "10");
    test_expr!("let lexer = Lexer { len: 10 }; println(1 < lexer.len);", "true");
    test_expr!("let lexer = Lexer { len: 10 }; lexer.len = 11; println(lexer.len);", "11");
    test_expr!(
        "let lexer = Lexer { str: \"abc\" }; lexer.str = lexer.str[0..2]; println(lexer.str)",
        "ab"
    );
    test_expr!("println('a')", "a");
    test_expr!(r#"println('/' == '/')"#, "true");
    test_expr!(r#"println("/" == '/')"#, "true");
    test_expr!(r#"println('/' == "/")"#, "true");
    test_expr!(r#"println("/" == "/")"#, "true");
    test_expr!(r#"println("/" == "/")"#, "true");
    test_expr!("enum Emotion { Happy }; println(Emotion.Happy)", "Happy");
    test_expr!("if 5 < 1 { println(true); } else { println(false); } ", "false");
    test_expr!(r#"println("Hello, World!"[5])"#, ",");
    test_expr!(r#"println("Hello, World!"[7..13])"#, "World!");
    test_expr!(r#"if false && true {} else if true && false {} else { println("Hi"); }"#, "Hi");
    test_expr!(r#"if true { println("a"); } else if false {} else {}"#, "a");
    test_expr!(r#"let tok; tok = "a"; println(tok);"#, "a");
    test_expr!("Point { x: 0, y: 0 }", "");
}
