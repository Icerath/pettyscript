use std::borrow::Cow;

use crate::{
    codegen,
    parser::{Ast, parse},
    vm,
};

fn exec_vm(bytecode: &[u8]) -> String {
    let mut output = vec![];
    // Safety: All tests rely on codegen.
    unsafe { vm::execute_bytecode_with(bytecode, &mut output).unwrap() };
    std::str::from_utf8(&output).unwrap().trim().to_owned()
}

macros::generate_integration_tests! {}

#[test]
fn test_fizzbuzz_example() {
    let src = include_str!("../examples/fizzbuzz.pty");
    let ast = parse(src).unwrap();
    let ast = Ast { src, body: &ast };
    let code = codegen::codegen(ast).unwrap();
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
#[cfg(not(miri))]
fn test_lexer_example() {
    use logos::Logos;

    use crate::lexer::Token;
    let fizzbuzz_src = include_str!("../examples/fizzbuzz.pty");
    let src = include_str!("../examples/lexer.pty");
    let ast = parse(src).unwrap();
    let ast = Ast { src, body: &ast };
    let code = codegen::codegen(ast).unwrap();
    let result = exec_vm(&code);

    let mut expected = String::new();
    for token in Token::lexer(fizzbuzz_src) {
        let token = token.unwrap();
        expected.push_str(&format!("{:?}\n", token.kind()));
    }
    assert_eq!(result, expected.trim());
}

macro_rules! test_expr {
    ($expr: literal, $expected: expr) => {{
        let src = concat!($expr, ";");
        let ast = parse(src).unwrap();
        let ast = Ast { src, body: &ast };
        let bytecode = codegen::codegen(ast).unwrap();
        let output = exec_vm(&bytecode);
        assert_eq!(output, $expected);
    }};
}

macro_rules! test_fails {
    ($name: ident, $src: literal) => {
        #[test]
        #[should_panic]
        fn $name() {
            let src = concat!($src, ";");
            let ast = match parse(src) {
                Ok(ast) => ast,
                Err(_) => {
                    eprintln!("Failed to parse");
                    return;
                }
            };
            let ast = Ast { src, body: &ast };
            codegen::codegen(ast).unwrap();
        }
    };
}

test_fails!(fail_arr, "let arr: array[i32] = ['1']");
test_fails!(fail_map, "let map: map[i32, char] = #{'1': 2 }");
test_fails!(zst_array_literals, "let arr = [null];");
test_fails!(zst_array_type, "let arr: array[null] = [];");
test_fails!(zst_map_type, "let map: map[int, null] = #{};");
test_fails!(test_illegal_arrays, "let array = []; array.push(1);");

#[test]
fn for_loop() {
    test_expr!(r#"for i in 0..=5 { println(f"{i}"); }"#, "0\n1\n2\n3\n4\n5");
    test_expr!(r#"for i in 0..=5 { if i == 0 { continue; } println(f"{i}"); }"#, "1\n2\n3\n4\n5");
    test_expr!(r#"for i in 0..=5 { if i == 4 { break; } println(f"{i}"); }"#, "0\n1\n2\n3");
    test_expr!(
        r#"fn main() { for i in 0..=5 { if i == 4 { return; } println(f"{i}"); } }"#,
        "0\n1\n2\n3"
    );
}

#[test]
fn structs() {
    test_expr!("struct Point {x:int,y:int} Point { x: 0, y: 0 }", "");
    test_expr!(
        r#"struct Lexer {str:str} let lexer = Lexer { str: "abc" }; lexer.str = lexer.str[0..2]; println(f"{lexer.str}")"#,
        "ab"
    );
    test_expr!(r#"struct A {str:int} println(f"{A { str: 1 }}")"#, "{ 1 }");
    test_expr!(r#"struct A {name:str} println(f"{(A { name: "Bob" }).name}")"#, "Bob");
    test_expr!(
        r#"struct Lexer {len:int}let lexer = Lexer { len: 10 }; println(f"{lexer.len}");"#,
        "10"
    );
    test_expr!(
        r#"struct Lexer{len:int} let lexer = Lexer { len: 10 }; println(f"{1 < lexer.len}");"#,
        "true"
    );
    test_expr!(
        r#"struct Lexer{len:int} let lexer = Lexer { len: 10 }; lexer.len = 11; println(f"{lexer.len}");"#,
        "11"
    );
}

#[test]
fn while_loops() {
    test_expr!(
        r#"let i: int = 0; while true { if i == 4 { break; } println(f"{i}"); i = i + 1; }"#,
        "0\n1\n2\n3"
    );
}

#[test]
fn if_stmt() {
    test_expr!(r#"if false && true {} else if true && false {} else { println("Hi"); }"#, "Hi");
    test_expr!(r#"if true { println("a"); } else if false {} else {}"#, "a");
    test_expr!(r#"if 5 < 1 { println(f"{true}"); } else { println(f"{false}"); } "#, "false");
}
