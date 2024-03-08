use vm::{
    ast::{Expression, Keyword, Literal, UnaryOp},
    prelude::PtyStr,
};
use winnow::{
    ascii,
    combinator::{alt, cut_err, delimited, opt, preceded, separated, seq},
    error::StrContext,
    token::take_while,
    Parser,
};

use crate::{
    binop::bin_expr,
    new_str,
    statement::{block, sep_params},
    ws, Result,
};

pub fn expression(input: &mut &str) -> Result<Expression> {
    alt((line_comment.map(|s| Expression::LineComment(s.into())), bin_expr)).parse_next(input)
}

pub fn value_expr(input: &mut &str) -> Result<Expression> {
    alt((unary_expr, value_expr_raw)).parse_next(input)
}

pub fn value_expr_raw(input: &mut &str) -> Result<Expression> {
    alt((
        keyword.map(Expression::Keyword),
        literal.map(Expression::Literal),
        ident.map(Expression::Ident),
    ))
    .parse_next(input)
}

pub fn unary_expr(input: &mut &str) -> Result<Expression> {
    use Expression::UnaryExpr;
    seq!(UnaryExpr { op: unary_op, expr: cut_err(expression.map(Box::new)) })
        .context(StrContext::Label("Unary"))
        .parse_next(input)
}
pub fn unary_op(input: &mut &str) -> Result<UnaryOp> {
    alt(('!'.value(UnaryOp::Not), '-'.value(UnaryOp::Neg))).parse_next(input)
}

pub fn keyword(input: &mut &str) -> Result<Keyword> {
    alt(("break".map(|_| Keyword::Break), "continue".map(|_| Keyword::Continue), r#return))
        .context(StrContext::Label("keyword"))
        .parse_next(input)
}
pub fn r#return(input: &mut &str) -> Result<Keyword> {
    preceded("return", opt(expression.map(Box::new))).map(Keyword::Return).parse_next(input)
}

pub fn ident(input: &mut &str) -> Result<PtyStr> {
    take_while(1.., ident_char)
        .recognize()
        .map(new_str)
        .context(StrContext::Label("ident"))
        .parse_next(input)
}
pub const fn ident_char(c: char) -> bool {
    matches!(c, 'a'..='z' | 'A'..='Z' | '_')
}

pub fn literal(input: &mut &str) -> Result<Literal> {
    alt((
        closure,
        bool.map(Literal::Bool),
        float.map(Literal::Float),
        int.map(Literal::Int),
        string.map(Literal::String),
        list.map(Literal::List),
    ))
    .parse_next(input)
}

pub fn closure(input: &mut &str) -> Result<Literal> {
    use Literal::Closure;
    seq!(Closure {
        _: ('|', ws),
        params: sep_params,
        _: (ws, '|', ws),
        block: block,
    })
    .parse_next(input)
}

pub fn bool(input: &mut &str) -> Result<bool> {
    alt(("true".value(true), "false".value(false))).parse_next(input)
}

pub fn float(input: &mut &str) -> Result<f64> {
    (int, '.', int).recognize().map(|s| s.parse().unwrap()).parse_next(input)
}

pub fn int(input: &mut &str) -> Result<i64> {
    ascii::dec_int(input)
}

pub fn string(input: &mut &str) -> Result<PtyStr> {
    delimited('"', take_while(0.., |c| c != '"').recognize(), '"').map(new_str).parse_next(input)
}

pub fn list(input: &mut &str) -> Result<Box<[Expression]>> {
    delimited('[', sep_expr, ']').parse_next(input)
}

pub fn sep_expr(input: &mut &str) -> Result<Box<[Expression]>> {
    separated(0.., delimited(ws, expression, ws), ',').map(Vec::into).parse_next(input)
}

pub fn line_comment<'a>(input: &mut &'a str) -> Result<&'a str> {
    delimited("//", take_while(0.., |c| c != '\n'), "\n").parse_next(input)
}
