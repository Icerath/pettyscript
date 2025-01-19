use logos::Logos;

use crate::lexer::Token;

#[test]
fn test_examples() {
    assert!(Token::lexer(include_str!("../examples/fizzbuzz.pty"))
        .collect::<Result<Vec<_>, _>>()
        .is_ok());

    assert!(Token::lexer(include_str!("../examples/lexer.pty"))
        .collect::<Result<Vec<_>, _>>()
        .is_ok());
}
