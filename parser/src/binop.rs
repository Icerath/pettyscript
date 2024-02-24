use vm::ast::{BinOp, Expression};
use winnow::{
    combinator::{alt, delimited, preceded, repeat},
    Parser,
};

use crate::{
    expression::{unary_expr, value_expr},
    ws,
};

type Result<T = Expression> = crate::Result<T>;

pub fn bin_expr(input: &mut &str) -> Result {
    range(input)
}

fn range(input: &mut &str) -> Result {
    (logical_or, repeat(0.., (binop_range, logical_or))).map(fold_exprs).parse_next(input)
}

fn binop_range(input: &mut &str) -> Result<BinOp> {
    ws.parse_next(input)?;
    alt(("..=".value(BinOp::RangeInclusive), "..".value(BinOp::RangeExclusive))).parse_next(input)
}

fn logical_or(input: &mut &str) -> Result {
    (logical_and, repeat(0.., (preceded(ws, "||".value(BinOp::Or)), logical_and)))
        .map(fold_exprs)
        .parse_next(input)
}

fn logical_and(input: &mut &str) -> Result {
    (comparison, repeat(0.., (preceded(ws, "&&".value(BinOp::And)), comparison)))
        .map(fold_exprs)
        .parse_next(input)
}

fn comparison(input: &mut &str) -> Result {
    (lower, (repeat(0.., (binop_comp, lower)))).map(fold_exprs).parse_next(input)
}

fn binop_comp(input: &mut &str) -> Result<BinOp> {
    ws.parse_next(input)?;
    alt((
        "<=".value(BinOp::LtEq),
        ">=".value(BinOp::GtEq),
        "==".value(BinOp::Eq),
        "!=".value(BinOp::Ne),
        '<'.value(BinOp::Lt),
        '>'.value(BinOp::Gt),
    ))
    .parse_next(input)
}

fn lower(input: &mut &str) -> Result {
    (upper, repeat(0.., (binop_lower, upper))).map(fold_exprs).parse_next(input)
}

fn binop_lower(input: &mut &str) -> Result<BinOp> {
    ws.parse_next(input)?;
    alt(('+'.value(BinOp::Add), '-'.value(BinOp::Sub))).parse_next(input)
}

fn upper(input: &mut &str) -> Result {
    (get_item, repeat(0.., (binop_upper, get_item))).map(fold_exprs).parse_next(input)
}

fn binop_upper(input: &mut &str) -> Result<BinOp> {
    ws.parse_next(input)?;
    alt(('*'.value(BinOp::Mul), '/'.value(BinOp::Div), '%'.value(BinOp::Mod))).parse_next(input)
}

fn get_item(input: &mut &str) -> Result {
    (factor, repeat(0.., ('.'.value(BinOp::Dot), factor))).map(fold_exprs).parse_next(input)
}

fn factor(input: &mut &str) -> Result {
    ws.parse_next(input)?;
    alt((paren_bin_expr, value_expr, unary_expr)).parse_next(input)
}

fn paren_bin_expr(input: &mut &str) -> Result {
    delimited('(', bin_expr, ')').parse_next(input)
}

fn fold_exprs((initial, remainder): (Expression, Vec<(BinOp, Expression)>)) -> Expression {
    remainder
        .into_iter()
        .fold(initial, |acc, (op, expr)| Expression::BinExpr { op, args: Box::new((acc, expr)) })
}
