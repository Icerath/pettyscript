use vm::{
    ast::{Expression, Keyword, Literal, UnaryOp},
    object::PtyStr,
};
use winnow::{
    ascii,
    combinator::{alt, delimited, opt, repeat, separated, seq},
    error::StrContext,
    token::{one_of, take_while},
    Parser,
};

use crate::{
    binop::bin_expr,
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
        fn_call,
        literal.map(Expression::Literal),
        ident.map(Expression::Ident),
    ))
    .parse_next(input)
}

pub fn unary_expr(input: &mut &str) -> Result<Expression> {
    let unary_op = alt((
        '!'.value(UnaryOp::Not),
        //'+'.value(UnaryOp::Plus),
        '-'.value(UnaryOp::Neg),
    ));

    // FIXME: alt((value, expression))
    (unary_op, expression.map(Box::new))
        .map(|(op, expr)| Expression::UnaryExpr { op, expr })
        .parse_next(input)
}

pub fn fn_call(input: &mut &str) -> Result<Expression> {
    use Expression::FuncCall;
    seq!(FuncCall {
        name: ident,
        _: ws,
        args: delimited('(', sep_expr, ')')
    })
    .context(StrContext::Label("fn call"))
    .parse_next(input)
}

pub fn keyword(input: &mut &str) -> Result<Keyword> {
    alt((
        "break".map(|_| Keyword::Break),
        ("return", opt(expression)).map(|(_, expr)| Keyword::Return(expr.map(Box::new))),
    ))
    .context(StrContext::Label("keyword"))
    .parse_next(input)
}

pub fn ident(input: &mut &str) -> Result<PtyStr> {
    fn ident_char(c: char) -> bool {
        matches!(c, 'a'..='z' | 'A'..='Z' | '_')
    }
    repeat(1.., one_of(ident_char))
        .map(String::into)
        .context(StrContext::Label("ident"))
        .parse_next(input)
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
    (int, '.', int).recognize().map(|s: &str| s.parse().unwrap()).parse_next(input)
}

pub fn int(input: &mut &str) -> Result<i64> {
    ascii::dec_int(input)
}

pub fn string(input: &mut &str) -> Result<PtyStr> {
    delimited('"', repeat(0.., one_of(|c| c != '"')), '"').map(String::into).parse_next(input)
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
