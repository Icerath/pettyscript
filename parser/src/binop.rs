use crate::*;

type Result<T = Expression> = crate::Result<T>;

pub fn bin_expr(input: &mut &str) -> Result {
    condition(input)
}

fn condition(input: &mut &str) -> Result {
    let initial = comparison(input)?;
    let remainder = repeat(0.., (binop_cond, comparison)).parse_next(input)?;
    Ok(fold_exprs(initial, remainder))
}

fn binop_cond(input: &mut &str) -> Result<BinOp> {
    ws.parse_next(input)?;
    alt(("&&".value(BinOp::And), "||".value(BinOp::Or))).parse_next(input)
}

fn comparison(input: &mut &str) -> Result {
    let initial = lower(input)?;
    let remainder = repeat(0.., (binop_comp, lower)).parse_next(input)?;
    Ok(fold_exprs(initial, remainder))
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
    let initial = upper(input)?;
    let remainder = repeat(0.., (binop_lower, upper)).parse_next(input)?;
    Ok(fold_exprs(initial, remainder))
}

fn binop_lower(input: &mut &str) -> Result<BinOp> {
    ws.parse_next(input)?;
    alt(('+'.value(BinOp::Add), '-'.value(BinOp::Sub))).parse_next(input)
}

fn upper(input: &mut &str) -> Result {
    let initial = get_item(input)?;
    let remainder = repeat(0.., (binop_upper, get_item)).parse_next(input)?;
    Ok(fold_exprs(initial, remainder))
}

fn binop_upper(input: &mut &str) -> Result<BinOp> {
    ws.parse_next(input)?;
    alt(('*'.value(BinOp::Mul), '/'.value(BinOp::Div), '%'.value(BinOp::Mod))).parse_next(input)
}

fn get_item(input: &mut &str) -> Result {
    let initial = factor(input)?;
    let remainder = repeat(0.., ('.'.value(BinOp::Dot), get_item_suffix)).parse_next(input)?;
    Ok(fold_exprs(initial, remainder))
}

fn get_item_suffix(input: &mut &str) -> Result {
    alt((fn_call, ident.map(Expression::Ident))).parse_next(input)
}

fn factor(input: &mut &str) -> Result {
    ws.parse_next(input)?;
    alt((paren_bin_expr, value_expr, unary_expr)).parse_next(input)
}

fn paren_bin_expr(input: &mut &str) -> Result {
    delimited('(', bin_expr, ')').parse_next(input)
}

fn fold_exprs(initial: Expression, remainder: Vec<(BinOp, Expression)>) -> Expression {
    remainder
        .into_iter()
        .fold(initial, |acc, (op, expr)| Expression::BinExpr { op, args: Box::new((acc, expr)) })
}
