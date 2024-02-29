use vm::ast::{BinOp, Expression};
use winnow::{
    combinator::{alt, delimited, opt, preceded, repeat},
    Parser,
};

use crate::{
    expression::{sep_expr, unary_expr, value_expr},
    ws,
};

type Result<T = Expression> = crate::Result<T>;

pub fn bin_expr(input: &mut &str) -> Result {
    range(input)
}

fn range(input: &mut &str) -> Result {
    require_parens(logical_or, alt((op("..="), op(".."))), logical_or).parse_next(input)
}

fn logical_or(input: &mut &str) -> Result {
    left_to_right(logical_and, op("||"), logical_and).parse_next(input)
}

fn logical_and(input: &mut &str) -> Result {
    left_to_right(comparison, op("&&"), comparison).parse_next(input)
}

fn comparison(input: &mut &str) -> Result {
    require_parens(lower, alt((op("<="), op(">="), op("=="), op("!="), op("<"), op(">"))), lower)
        .parse_next(input)
}

fn lower(input: &mut &str) -> Result {
    left_to_right(upper, alt((op("+"), op("-"))), upper).parse_next(input)
}

fn upper(input: &mut &str) -> Result {
    (get_item, repeat(0.., (alt((op("*"), op("/"), op("%"))), get_item)))
        .map(fold_exprs)
        .parse_next(input)
}

fn get_item(input: &mut &str) -> Result {
    (func_call, repeat(0.., (op("."), func_call))).map(fold_exprs).parse_next(input)
}

fn func_call(input: &mut &str) -> Result {
    (factor, opt(delimited('(', sep_expr, ')')))
        .map(|(expr, args)| match args {
            Some(args) => Expression::FuncCall { expr: Box::new(expr), args },
            None => expr,
        })
        .parse_next(input)
}

fn factor(input: &mut &str) -> Result {
    preceded(ws, alt((paren_bin_expr, value_expr, unary_expr))).parse_next(input)
}

fn paren_bin_expr(input: &mut &str) -> Result {
    delimited('(', bin_expr, ')').parse_next(input)
}

fn left_to_right<'a>(
    lhs: impl Parser<&'a str, Expression, crate::Error>,
    op: impl Parser<&'a str, BinOp, crate::Error>,
    rhs: impl Parser<&'a str, Expression, crate::Error>,
) -> impl Parser<&'a str, Expression, crate::Error> {
    (lhs, repeat(0.., (op, rhs))).map(fold_exprs)
}

fn require_parens<'a>(
    lhs: impl Parser<&'a str, Expression, crate::Error>,
    op: impl Parser<&'a str, BinOp, crate::Error>,
    rhs: impl Parser<&'a str, Expression, crate::Error>,
) -> impl Parser<&'a str, Expression, crate::Error> {
    (lhs, opt((op, rhs))).map(|(lhs, opt)| match opt {
        Some((op, rhs)) => Expression::BinExpr { op, args: Box::new((lhs, rhs)) },
        None => lhs,
    })
}

fn fold_exprs((initial, remainder): (Expression, Vec<(BinOp, Expression)>)) -> Expression {
    remainder
        .into_iter()
        .fold(initial, |acc, (op, expr)| Expression::BinExpr { op, args: Box::new((acc, expr)) })
}

fn op(op: &str) -> impl Parser<&str, BinOp, crate::Error> {
    preceded(ws, op.value(BinOp::try_from(op).unwrap()))
}
