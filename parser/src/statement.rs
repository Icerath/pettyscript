use vm::{
    ast::{BinOp, IfStatement, Node, Statement},
    object::PtyStr,
};
use winnow::{
    combinator::{alt, delimited, repeat, seq},
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
        op_decl,
        op_assign,
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

pub fn func_params(input: &mut &str) -> Result<Box<[PtyStr]>> {
    delimited('(', sep_params, ')').parse_next(input)
}

pub fn sep_params(input: &mut &str) -> Result<Box<[PtyStr]>> {
    repeat(0.., delimited(ws, ident, ws)).map(Vec::into_boxed_slice).parse_next(input)
}

pub fn var_decl(input: &mut &str) -> Result<Statement> {
    use Statement::VarDecl;
    seq!(VarDecl {
        _: ("let", ws),
        name: ident,
        _: (ws, '=', ws),
        expr: expression,
    })
    .context(StrContext::Label("var_decl"))
    .parse_next(input)
}

pub fn var_assign(input: &mut &str) -> Result<Statement> {
    use Statement::VarAssign;
    seq!(VarAssign {
        name: ident,
        _: (ws, '=', ws),
        expr: expression,
    })
    .context(StrContext::Label("var_decl"))
    .parse_next(input)
}

pub fn op_decl(input: &mut &str) -> Result<Statement> {
    use Statement::OpDecl;
    seq!(OpDecl {
        _: ("let", ws),
        name: ident,
        _: ws,
        op: op_symbol,
        _: ('=', ws),
        expr: expression,
    })
    .context(StrContext::Label("var_decl"))
    .parse_next(input)
}

pub fn op_assign(input: &mut &str) -> Result<Statement> {
    use Statement::OpAssign;
    seq!(OpAssign {
        name: ident,
        _: ws,
        op: op_symbol,
        _: ('=', ws),
        expr: expression,
    })
    .context(StrContext::Label("var_decl"))
    .parse_next(input)
}

#[allow(clippy::enum_glob_use)]
fn op_symbol(input: &mut &str) -> Result<BinOp> {
    use BinOp::*;
    alt((
        "<=".value(LtEq),
        ">=".value(GtEq),
        "==".value(Eq),
        "!=".value(Ne),
        "&&".value(And),
        "||".value(Or),
        '+'.value(Add),
        '-'.value(Sub),
        '*'.value(Mul),
        '/'.value(Div),
        '%'.value(Mod),
        '<'.value(Lt),
        '>'.value(Gt),
        "^".value(Xor),
    ))
    .parse_next(input)
}

pub fn block(input: &mut &str) -> Result<Box<[Node]>> {
    alt((single_block, many_block)).parse_next(input)
}
pub fn single_block(input: &mut &str) -> Result<Box<[Node]>> {
    (':', ws, node).map(|(_, _, node)| [node].into()).parse_next(input)
}
pub fn many_block(input: &mut &str) -> Result<Box<[Node]>> {
    delimited('{', sep_node, '}').parse_next(input)
}

pub fn sep_node(input: &mut &str) -> Result<Box<[Node]>> {
    repeat(0.., delimited(ws, node, ws)).map(Vec::into_boxed_slice).parse_next(input)
}

pub fn for_loop(input: &mut &str) -> Result<Statement> {
    use Statement::ForLoop;
    seq!(ForLoop {
        _: ("for", ws),
        ident: ident,
        _: (ws, "in", ws),
        iter: expression,
        _: ws,
        block: block
    })
    .context(StrContext::Label("for loop"))
    .parse_next(input)
}

pub fn while_loop(input: &mut &str) -> Result<Statement> {
    use Statement::WhileLoop;
    seq!(WhileLoop {
        _: ("while", ws),
        expr: expression,
        _: ws,
        block: block,
    })
    .context(StrContext::Label("while loop"))
    .parse_next(input)
}

pub fn if_statement(input: &mut &str) -> Result<IfStatement> {
    seq!(IfStatement {
        _: ("if", ws),
        condition: expression,
        _: ws,
        block: block,
        _: ws,
        or_else: or_else
    })
    .parse_next(input)
}

pub fn or_else(input: &mut &str) -> Result<Option<Box<Node>>> {
    if ("else", ws).parse_next(input).is_err() {
        return Ok(None);
    }
    alt((if_statement.map(Node::from), block.map(Node::block)))
        .map(Box::new)
        .map(Some)
        .parse_next(input)
}
