use crate::{codegen, parser::parse, vm};

#[test]
fn test_examples() {
    let _ = parse(include_str!("../examples/fizzbuzz.pty")).unwrap();
    let _ = parse(include_str!("../examples/lexer.pty")).unwrap();
}

macro_rules! test_expr {
    ($expr: literal, $expected: literal) => {
        let ast = parse(concat!("fn main() { ", $expr, "; }")).unwrap();
        let bytecode = codegen::codegen(&ast);
        let mut output = vec![];
        vm::execute_bytecode_with(&mut output, &bytecode).unwrap();
        assert_eq!(String::from_utf8(output).unwrap().trim(), $expected);
    };
}

#[test]
fn test_obvious() {
    test_expr!("println(1 + 2)", "3");
}
