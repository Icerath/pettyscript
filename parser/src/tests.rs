use vm::ast::{Literal, Node};

use crate::{parse, parse_many};

fn config() -> formatter::Config {
    let mut config = formatter::Config::default();
    config.indent_level = 0;
    config.replace_newline_with_space = true;
    config
}

macro_rules! test_expected {
    ($input:literal) => {
        test_expected!($input, $input)
    };
    ($input:literal, $output:literal $(,)?) => {
        assert_eq!(formatter::format_one(&parse($input).unwrap(), config()).trim(), $output);
    };
}

#[test]
fn literals() {
    test_expected!(r#"{ true false 1 1.5 true "string" ident ["hello", "world"] }"#);
    assert_eq!(parse("true"), Ok(Node::from(Literal::Bool(true))));
    assert_eq!(parse("false"), Ok(Node::from(Literal::Bool(false))));
}
#[test]
fn for_loop() {
    test_expected!(r#"for i in expr: print("Hello")"#);
}
#[test]
fn while_loop() {
    test_expected!(r#"while true: print("Hello")"#);
}
#[test]
fn test_if_statement() {
    test_expected!("if a {}");
    test_expected!(r#"if a {} else if b {} else: "hi""#);
}
#[test]
fn var_decl() {
    test_expected!("let a: int = 2");
}
#[test]
fn fn_call() {
    test_expected!("print(1, 2, 3)");
    test_expected!("(|x: int|: x * 2)(4)");
}
#[test]
fn fn_decl() {
    test_expected!("fn hi() {}");
    test_expected!("fn print(s): print(s)");
    test_expected!("fn add(x, y): x + y");
}
#[test]
fn class_decl() {
    test_expected!("class Unit {}");
    test_expected!("class Point { x, y }");
    test_expected!("class Point { x: float, y: float }");
}
#[test]
fn bin_expr() {
    test_expected!("1 + 1");
    test_expected!("1 + 1 * 1", "1 + (1 * 1)");
    test_expected!("(1 + 1) * 1", "(1 + 1) * 1");
    test_expected!("(1..2)..=3", "(1..2)..=3");
    test_expected!("(1 == 2) == 3", "(1 == 2) == 3");
    test_expected!("1 | 2 ^ 3 & 4 >> 5 << 6", "1 | (2 ^ (3 & (4 >> 5) << 6))");

    assert!(parse("1 == 2 == 3").is_err());
}
#[test]
fn unary_op() {
    test_expected!("! true", "!true");
    test_expected!("- 1", "-1");
}
#[test]
fn closures() {
    test_expected!("|i|: i*i", "|i|: i * i");
}

mod examples {
    macro_rules! test_example {
        ($name:ident) => {
            #[test]
            fn $name() {
                let input = include_str!(concat!("../../examples/", stringify!($name), ".pty"));
                let ast = super::parse_many(input).unwrap();

                let output = formatter::format_many(&ast, formatter::Config::default());
                assert_eq!(input, output);
            }
        };
    }
    test_example!(fizzbuzz);
    test_example!(hello_world);
    test_example!(sum_squares);
    test_example!(while_loop);
    test_example!(literals);
    test_example!(classes);
}
