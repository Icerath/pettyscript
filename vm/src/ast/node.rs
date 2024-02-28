use crate::prelude::*;

#[derive(Debug, PartialEq)]
pub enum Node {
    Statement(Statement),
    Expression(Expression),
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    FuncDecl {
        name: PtyStr,
        params: Box<[Param]>,
        /* ret_type: PtyStr , */
        block: Box<[Node]>,
    },
    VarDecl {
        param: Param,
        expr: Expression,
    },
    VarAssign {
        name: PtyStr,
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

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Param {
    pub ident: PtyStr,
    pub ty: Option<Type>,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Type {
    pub segments: Box<[PtyStr]>,
}

#[derive(Debug, PartialEq)]
pub struct IfStatement {
    pub condition: Expression,
    pub block: Box<[Node]>,
    pub or_else: Option<Box<Node>>,
}

#[derive(Debug, PartialEq)]
pub enum Expression {
    LineComment(String),
    Keyword(Keyword),
    Ident(PtyStr),
    Literal(Literal),
    FuncCall { expr: Box<Expression>, args: Box<[Expression]> },
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

#[derive(Debug, PartialEq)]
pub enum Literal {
    Bool(bool),
    Int(i64),
    Float(f64),
    String(PtyStr),
    List(Box<[Expression]>),
    Tuple(Box<[Expression]>),
    Map(Box<[(Expression, Expression)]>),
    Closure { params: Box<[Param]>, block: Box<[Node]> },
}

#[derive(Debug, PartialEq)]
pub enum Keyword {
    Break,
    Return(Option<Box<Expression>>),
}

impl BinOp {
    #[must_use]
    pub const fn symbol(self) -> &'static str {
        match self {
            Self::And => "&&",
            Self::Or => "||",
            Self::Xor => "^",

            Self::Lt => "<",
            Self::LtEq => "<=",
            Self::Gt => ">",
            Self::GtEq => ">=",
            Self::Eq => "==",
            Self::Ne => "!=",

            Self::Add => "+",
            Self::Sub => "-",

            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",

            Self::Dot => ".",

            Self::RangeInclusive => "..=",
            Self::RangeExclusive => "..",
        }
    }
}
