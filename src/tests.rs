use crate::parser::Parser;

#[test]
fn test_examples() {
    let _ = Parser::new(include_str!("../examples/fizzbuzz.pty")).parse_root().unwrap();
    let _ = Parser::new(include_str!("../examples/lexer.pty")).parse_root().unwrap();
}
