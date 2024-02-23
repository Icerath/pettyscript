#![allow(unused_imports)]

pub mod binop;
mod expression;
mod statement;

#[cfg(test)]
mod tests;

use binop::bin_expr;
use expression::{expression, fn_call, ident, unary_expr, value_expr};
use statement::{sep_node, statement};
use vm::ast::{node::Literal, BinOp, Expression, IfStatement, Keyword, Node, Statement, UnaryOp};
use vm::prelude::PtyStr;
use winnow::{
    ascii::{dec_int, float},
    combinator::{alt, cut_err, delimited, opt, repeat, separated, seq, terminated},
    error::{ErrMode, ParseError, StrContext},
    token::{one_of, take_while},
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
