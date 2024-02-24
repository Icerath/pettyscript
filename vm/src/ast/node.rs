use crate::prelude::*;

#[derive(PartialEq)]
pub enum Node {
    Statement(Statement),
    Expression(Expression),
}

#[derive(PartialEq)]
pub enum Statement {
    FuncDecl {
        name: PtyStr,
        params: Box<[PtyStr]>,
        /* ret_type: PtyStr , */ block: Box<[Node]>,
    },
    VarDecl {
        name: PtyStr,
        expr: Expression,
    },
    VarAssign {
        name: PtyStr,
        expr: Expression,
    },
    OpDecl {
        name: PtyStr,
        op: BinOp,
        expr: Expression,
    },
    OpAssign {
        name: PtyStr,
        op: BinOp,
        expr: Expression,
    },
    Block(Box<[Node]>),
    ForLoop {
        ident: PtyStr,
        iter: Expression,
        block: Box<[Node]>,
    },
    WhileLoop {
        expr: Expression,
        block: Box<[Node]>,
    },
    IfStatement(IfStatement),
}

#[derive(PartialEq)]
pub struct IfStatement {
    pub condition: Expression,
    pub block: Box<[Node]>,
    pub or_else: Option<Box<Node>>,
}

#[derive(PartialEq)]
pub enum Expression {
    LineComment(String),
    Keyword(Keyword),
    Ident(PtyStr),
    Literal(Literal),
    FuncCall { name: PtyStr, args: Box<[Expression]> },
    BinExpr { op: BinOp, args: Box<(Expression, Expression)> },
    UnaryExpr { op: UnaryOp, expr: Box<Expression> },
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BinOp {
    Or,
    And,
    Xor,

    Lt,
    LtEq,
    Gt,
    GtEq,
    Eq,
    Ne,

    Add,
    Sub,

    Mul,
    Div,
    Mod,

    Dot,

    RangeInclusive,
    RangeExclusive,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum UnaryOp {
    Not,
    Neg,
    //Splat,
}

#[derive(PartialEq)]
pub enum Literal {
    Bool(bool),
    Int(i64),
    Float(f64),
    String(PtyStr),
    List(Box<[Expression]>),
    Tuple(Box<[Expression]>),
    Map(Box<[(Expression, Expression)]>),
    Closure { params: Box<[PtyStr]>, block: Box<[Node]> },
}

#[derive(Debug, PartialEq)]
pub enum Keyword {
    Break,
    Return(Option<Box<Expression>>),
}
