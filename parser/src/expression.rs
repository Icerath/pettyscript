use crate::*;

pub fn expression(input: &mut &str) -> Result<Expression> {
    alt((
        line_comment.map(|s| Expression::LineComment(s.into())),
        fn_call,
        keyword.map(Expression::Keyword),
        literal.map(Expression::Literal),
        ident.map(Expression::Ident),
    ))
    .context(StrContext::Label("expr"))
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
        bool.map(Literal::Bool),
        float.map(Literal::Float),
        dec_int.map(Literal::Int),
        string.map(Literal::String),
        list.map(Literal::List),
    ))
    .parse_next(input)
}
pub fn bool(input: &mut &str) -> Result<bool> {
    alt(("true".value(true), "false".value(false))).parse_next(input)
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