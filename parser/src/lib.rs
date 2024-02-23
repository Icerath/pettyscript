#![allow(unused_imports)]

pub mod binop;
mod expression;
mod statement;

#[cfg(test)]
mod tests;

use expression::expression;
use statement::{sep_node, statement};
use vm::{ast::Node, prelude::PtyStr};
use winnow::{
    combinator::{alt, delimited},
    error::{ErrMode, ParseError},
    token::take_while,
    Parser,
};

pub type Error = winnow::error::ContextError;
pub type Result<T, E = ErrMode<Error>> = std::result::Result<T, E>;

pub fn parse(input: &str) -> Result<Node, ParseError<&str, Error>> {
    delimited(ws, node, ws).parse(input)
}

pub fn parse_many(input: &str) -> Result<Box<[Node]>, ParseError<&str, Error>> {
    sep_node.parse(input)
}

pub fn node(input: &mut &str) -> Result<Node> {
    alt((statement.map(Node::Statement), expression.map(Node::Expression))).parse_next(input)
}

pub fn ws<'a>(input: &mut &'a str) -> Result<&'a str> {
    const WS: &[char] = &[' ', '\t', '\r', '\n', ';'];
    take_while(0.., WS).parse_next(input)
}
