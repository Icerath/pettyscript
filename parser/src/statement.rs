use vm::ast::{
    node::{Param, Type},
    BinOp, IfStatement, Node, Statement,
};
use winnow::{
    combinator::{alt, cut_err, delimited, opt, preceded, repeat, separated, seq},
    error::StrContext,
    Parser,
};

use crate::{
    expression::{expression, ident},
    node, ws, Result,
};

pub fn statement(input: &mut &str) -> Result<Statement> {
    alt((
        fn_decl,
        var_decl,
        var_assign,
        block.map(Statement::Block),
        for_loop,
        while_loop,
        if_statement.map(Into::into),
    ))
    .parse_next(input)
}

pub fn fn_decl(input: &mut &str) -> Result<Statement> {
    use Statement::FuncDecl;
    seq!(FuncDecl {
        _: ("fn", ws),
        name: ident,
        _: ws,
        params: func_params,
        _: ws,
        block: block })
    .parse_next(input)
}

pub fn func_params(input: &mut &str) -> Result<Box<[Param]>> {
    delimited('(', sep_params, ')').parse_next(input)
}

pub fn sep_params(input: &mut &str) -> Result<Box<[Param]>> {
    repeat(0.., delimited(ws, param, ws)).map(Vec::into_boxed_slice).parse_next(input)
}

pub fn param(input: &mut &str) -> Result<Param> {
    (ident, opt(preceded((':', ws), type_path)))
        .map(|(ident, ty)| Param { ident, ty })
        .parse_next(input)
}

pub fn type_path(input: &mut &str) -> Result<Type> {
    separated(1.., ident, "::")
        .map(|values| Type { segments: Vec::into_boxed_slice(values) })
        .parse_next(input)
}

pub fn var_decl(input: &mut &str) -> Result<Statement> {
    ("let", ws).parse_next(input)?;

    cut_err((param, (ws, '='), expression))
        .map(|(param, _, expr)| Statement::VarDecl { param, expr })
        .context(StrContext::Label("let decl"))
        .parse_next(input)
}

pub fn var_assign(input: &mut &str) -> Result<Statement> {
    (ident, ws, opt(op_assign_symbol), '=', cut_err(expression))
        .map(|(name, _, op_symbol, _, expr)| match op_symbol {
            Some(op) => Statement::OpAssign { name, op, expr },
            None => Statement::VarAssign { name, expr },
        })
        .context(StrContext::Label("var assign"))
        .parse_next(input)
}

#[allow(clippy::enum_glob_use)]
fn op_assign_symbol(input: &mut &str) -> Result<BinOp> {
    use BinOp::*;
    alt((
        '+'.value(Add),
        '-'.value(Sub),
        '*'.value(Mul),
        '/'.value(Div),
        '%'.value(Mod),
        '^'.value(Xor),
    ))
    .parse_next(input)
}

pub fn block(input: &mut &str) -> Result<Box<[Node]>> {
    alt((single_block, many_block)).parse_next(input)
}

pub fn single_block(input: &mut &str) -> Result<Box<[Node]>> {
    ((':', ws), node).map(|(_, node)| [node].into()).parse_next(input)
}

pub fn many_block(input: &mut &str) -> Result<Box<[Node]>> {
    delimited('{', sep_node, '}').parse_next(input)
}

pub fn sep_node(input: &mut &str) -> Result<Box<[Node]>> {
    repeat(0.., delimited(ws, node, ws)).map(Vec::into_boxed_slice).parse_next(input)
}

pub fn for_loop(input: &mut &str) -> Result<Statement> {
    use Statement::ForLoop;
    ("for", ws).parse_next(input)?;
    cut_err(seq!(ForLoop {
        ident: ident,
        _: (ws, "in"),
        iter: expression,
        _: ws,
        block: block
    }))
    .context(StrContext::Label("for loop"))
    .parse_next(input)
}

pub fn while_loop(input: &mut &str) -> Result<Statement> {
    use Statement::WhileLoop;
    "while".parse_next(input)?;
    cut_err(seq!(WhileLoop { expr: expression, _: ws, block: block }))
        .context(StrContext::Label("while loop"))
        .parse_next(input)
}

pub fn if_statement(input: &mut &str) -> Result<IfStatement> {
    "if".parse_next(input)?;
    cut_err(seq!(IfStatement {
        condition: expression,
        _: ws,
        block: block,
        _: ws,
        or_else: or_else
    }))
    .parse_next(input)
}

pub fn or_else(input: &mut &str) -> Result<Option<Box<Node>>> {
    if ("else", ws).parse_next(input).is_err() {
        return Ok(None);
    }
    alt((if_statement.map(Node::from), block.map(Node::block)))
        .map(|node| Some(Box::new(node)))
        .parse_next(input)
}
