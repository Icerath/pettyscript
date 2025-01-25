use std::borrow::Cow;

use bstr::ByteSlice;
use logos::Logos;

use crate::{codegen, lexer::Token, parser::parse, vm};

fn exec_vm(bytecode: &[u8]) -> String {
    let mut output = vec![];
    vm::execute_bytecode_with(&mut output, bytecode).unwrap();
    output.to_str().unwrap().trim().to_owned()
}

#[test]
fn test_fizzbuzz_example() {
    let src = include_str!("../examples/fizzbuzz.pty");
    let ast = parse(src).unwrap();
    let code = codegen::codegen(&ast);
    let result = exec_vm(&code);

    let expected: String = (1..=100)
        .map(|i| match i {
            _ if i % 15 == 0 => "FizzBuzz\n".into(),
            _ if i % 3 == 0 => "Fizz\n".into(),
            _ if i % 5 == 0 => "Buzz\n".into(),
            _ => Cow::Owned(i.to_string() + "\n"),
        })
        .collect();

    assert_eq!(result, expected.trim());
}

#[test]
fn test_lexer_example() {
    let fizzbuzz_src = include_str!("../examples/fizzbuzz.pty");
    let src = include_str!("../examples/lexer.pty");
    let ast = parse(src).unwrap();
    let code = codegen::codegen(&ast);
    let result = exec_vm(&code);

    let mut expected = String::new();
    for token in Token::lexer(fizzbuzz_src) {
        let token = token.unwrap();
        expected.push_str(&format!("{:?}\n", token.kind()));
    }

    assert_eq!(result, expected.trim());
}

macro_rules! test_expr {
    ($expr: literal, $expected: expr) => {
        let ast = parse(concat!($expr, ";")).unwrap();
        let bytecode = codegen::codegen(&ast);
        let output = exec_vm(&bytecode);
        assert_eq!(output, $expected);
    };
}

#[test]
fn test_logical_and() {
    test_expr!("println(false && false)", "false");
    test_expr!("println(false && true)", "false");
    test_expr!("println(true && false)", "false");
    test_expr!("println(true && true)", "true");
}

#[test]
fn test_logical_or() {
    test_expr!("println(false || false)", "false");
    test_expr!("println(false || true)", "true");
    test_expr!("println(true || false)", "true");
    test_expr!("println(true || true)", "true");
}

#[test]
fn test_for_loop() {
    test_expr!("for i in 0..=5 { println(i); }", "0\n1\n2\n3\n4\n5");
    test_expr!("for i in 0..=5 { if i == 0 { continue; } println(i); }", "1\n2\n3\n4\n5");
    test_expr!("for i in 0..=5 { if i == 4 { break; } println(i); }", "0\n1\n2\n3");
    test_expr!("fn main() { for i in 0..=5 { if i == 4 { return; } println(i); } }", "0\n1\n2\n3");
}

#[test]
fn test_str_char_eq() {
    test_expr!(r#"println('/' == '/')"#, "true");
    test_expr!(r#"println("/" == '/')"#, "true");
    test_expr!(r#"println('/' == "/")"#, "true");
    test_expr!(r#"println("/" == "/")"#, "true");
    test_expr!(r#"println("/" == "/")"#, "true");
}

#[test]
fn test_character_literals() {
    test_expr!("println('a')", "a");
}

#[test]
fn test_enum_variants() {
    test_expr!("enum Emotion { Happy }; println(Emotion.Happy)", "Happy");
}

#[test]
fn test_structs() {
    test_expr!("Point { x: 0, y: 0 }", "");
    test_expr!(
        "let lexer = Lexer { str: \"abc\" }; lexer.str = lexer.str[0..2]; println(lexer.str)",
        "ab"
    );
    test_expr!("println(A { str: 1 })", "{ str: 1 }");
    test_expr!("println((A { name: \"Bob\" }).name)", "Bob");
    test_expr!("let lexer = Lexer { len: 10 }; println(lexer.len);", "10");
    test_expr!("let lexer = Lexer { len: 10 }; println(1 < lexer.len);", "true");
    test_expr!("let lexer = Lexer { len: 10 }; lexer.len = 11; println(lexer.len);", "11");
}

#[test]
fn test_int_literals() {
    test_expr!("println(0x1)", "1");
    test_expr!("println(0x18a968bc945df)", 0x18a968bc945dfu64.to_string());
    test_expr!("println(0b0110101011101001)", 0b0110101011101001.to_string());
    test_expr!("println(0o172364123752317)", 0o172364123752317u64.to_string());
}

#[test]
fn test_while_loops() {
    test_expr!(
        "let i = 0; while true { if i == 4 { break; } println(i); i = i + 1; }",
        "0\n1\n2\n3"
    );
}

#[test]
fn test_array_literals() {
    test_expr!("println([])", "[]");
    test_expr!(r#"println([1, 2, 3, "Go!"])"#, r#"[1, 2, 3, Go!]"#);
    test_expr!("let arr = []; array_push(arr, 1); println(arr)", "[1]");
    test_expr!("let arr = [1]; println(array_pop(arr)); println(arr);", "1\n[]");
}

#[test]
fn test_gt_lt() {
    test_expr!("println(1 < 2)", "true");
    test_expr!("println(5 > 4)", "true");
}

#[test]
fn test_str_len() {
    test_expr!("println(str_len(\"123456789\"))", "9");
}

#[test]
fn test_trim() {
    test_expr!(r#"println(trim("  \n   Hello, World!\n  "))"#, "Hello, World!");
}

#[test]
fn test_late_initialization() {
    test_expr!(r#"let tok; tok = "a"; println(tok);"#, "a");
}

#[test]
fn test_if_stmt() {
    test_expr!(r#"if false && true {} else if true && false {} else { println("Hi"); }"#, "Hi");
    test_expr!(r#"if true { println("a"); } else if false {} else {}"#, "a");
    test_expr!("if 5 < 1 { println(true); } else { println(false); } ", "false");
}

#[test]
fn test_string_slicing() {
    test_expr!(r#"println("Hello, World!"[5])"#, ",");
    test_expr!(r#"println("Hello, World!"[7..13])"#, "World!");
}
