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
#[cfg(not(miri))]
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
    test_expr!(r#"println(f"{false && false}")"#, "false");
    test_expr!(r#"println(f"{false && true}")"#, "false");
    test_expr!(r#"println(f"{true && false}")"#, "false");
    test_expr!(r#"println(f"{true && true}")"#, "true");
}

#[test]
fn test_logical_or() {
    test_expr!(r#"println(f"{false || false}")"#, "false");
    test_expr!(r#"println(f"{false || true}")"#, "true");
    test_expr!(r#"println(f"{true || false}")"#, "true");
    test_expr!(r#"println(f"{true || true}")"#, "true");
}

#[test]
fn test_for_loop() {
    test_expr!(r#"for i in 0..=5 { println(f"{i}"); }"#, "0\n1\n2\n3\n4\n5");
    test_expr!(r#"for i in 0..=5 { if i == 0 { continue; } println(f"{i}"); }"#, "1\n2\n3\n4\n5");
    test_expr!(r#"for i in 0..=5 { if i == 4 { break; } println(f"{i}"); }"#, "0\n1\n2\n3");
    test_expr!(
        r#"fn main() { for i in 0..=5 { if i == 4 { return; } println(f"{i}"); } }"#,
        "0\n1\n2\n3"
    );
}

#[test]
fn test_str_literal() {
    test_expr!(r#"println("\"")"#, "\"");
}

#[test]
fn test_str_char_eq() {
    test_expr!(r#"println(f"{'/' == '/'}")"#, "true");
    test_expr!(r#"println(f"{"/" == '/'}")"#, "true");
    test_expr!(r#"println(f"{'/' == "/"}")"#, "true");
    test_expr!(r#"println(f"{"/" == "/"}")"#, "true");
    test_expr!(r#"println(f"{"/" == "/"}")"#, "true");
}

#[test]
fn test_fstr() {
    test_expr!(r#"println(f"A"); "#, "A");
    test_expr!(r#"let x = 0; println(f"{x}"); "#, "0");
    test_expr!(r#"let x = 1; let y = 2; println(f"{x + y}"); "#, "3");
    test_expr!(r#"let x = 1; let y = 2; println(f"{"a" == "a"}"); "#, "true");
}

#[test]
fn test_character_literals() {
    test_expr!(r#"println(f"{'a'}")"#, "a");
}

#[test]
fn test_enum_variants() {
    test_expr!(r#"enum Emotion { Happy }; println(f"{Emotion.Happy}")"#, "Happy");
}

#[test]
fn test_structs() {
    test_expr!("struct Point {x:int,y:int} Point { x: 0, y: 0 }", "");
    test_expr!(
        r#"struct Lexer {str:str} let lexer = Lexer { str: "abc" }; lexer.str = lexer.str[0..2]; println(f"{lexer.str}")"#,
        "ab"
    );
    test_expr!(r#"struct A {str:int} println(f"{A { str: 1 }}")"#, "{ str: 1 }");
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
fn test_int_literals() {
    test_expr!(r#"println(f"{0x1}")"#, "1");
    test_expr!(r#"println(f"{0x18a968bc945df}")"#, 0x18a968bc945dfu64.to_string());
    test_expr!(r#"println(f"{0b0110101011101001}")"#, 0b0110101011101001.to_string());
    test_expr!(r#"println(f"{0o172364123752317}")"#, 0o172364123752317u64.to_string());
}

#[test]
fn test_while_loops() {
    test_expr!(
        r#"let i: int = 0; while true { if i == 4 { break; } println(f"{i}"); i = i + 1; }"#,
        "0\n1\n2\n3"
    );
}

#[test]
fn test_list_index() {
    test_expr!(r#"println(f"{[1][0]}")"#, "1");
}

#[test]
fn test_unary() {
    test_expr!(r#"println(f"{!false}")"#, "true");
    test_expr!(r#"println(f"{-123712}")"#, "-123712");
}

#[test]
fn test_maps() {
    test_expr!(
        r#"let hi = create_map(); hi.insert("Bob", 32); hi.insert("Alice", 34); println(f"{hi}")"#,
        "{Bob: 32, Alice: 34}"
    );
    test_expr!(
        r#"let hi = create_map(); hi.insert("Bob", 32); println(f"{hi.get("Bob")}"); hi.remove("Bob"); println(f"{hi}"); println(f"{hi.get("Bob")}");"#,
        "32\n{}\nnull"
    );
    test_expr!(
        r#"let hi = create_map(); hi.insert("Bob", 32); println(f"{hi.get("Bob")}");"#,
        "32"
    );
}

#[test]
fn test_array_literals() {
    // test_expr!(r#"println(f"{[]}")"#, "[]");
    test_expr!(r#"println(f"{[1, 2, 3]}")"#, r#"[1, 2, 3]"#);
    test_expr!(r#"let arr = [2]; arr.pop(); arr.push(1); println(f"{arr}")"#, "[1]");
    test_expr!(r#"let arr = [1]; println(f"{arr.pop()}"); println(f"{arr}");"#, "1\n[]");
}

#[test]
fn test_gt_lt() {
    test_expr!(r#"println(f"{1 < 2}")"#, "true");
    test_expr!(r#"println(f"{5 > 4}")"#, "true");
}

#[test]
fn test_str_len() {
    test_expr!(r#"println(f"{"123456789".len}")"#, "9");
}

#[test]
fn test_trim() {
    test_expr!(r#"println("  \n   Hello, World!\n  ".trim())"#, "Hello, World!");
}

#[test]
fn test_late_initialization() {
    test_expr!(r#"let tok: str; tok = "a"; println(f"{tok}");"#, "a");
}

#[test]
fn test_if_stmt() {
    test_expr!(r#"if false && true {} else if true && false {} else { println("Hi"); }"#, "Hi");
    test_expr!(r#"if true { println("a"); } else if false {} else {}"#, "a");
    test_expr!(r#"if 5 < 1 { println(f"{true}"); } else { println(f"{false}"); } "#, "false");
}

#[test]
fn test_string_slicing() {
    test_expr!(r#"println(f"{"Hello, World!"[5]}")"#, ",");
    test_expr!(r#"println("Hello, World!"[7..13])"#, "World!");
}
