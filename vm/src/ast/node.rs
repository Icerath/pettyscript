use crate::prelude::*;

#[derive(Debug, PartialEq)]
pub enum Node {
    Statement(Statement),
    Expression(Expression),
}

#[derive(Debug, PartialEq)]
pub enum Statement {
    FuncDecl { path: Type, params: Box<[Param]>, ret_type: Option<Type>, block: Block },
    ClassDecl { name: PtyStr, params: Box<[Param]> },
    VarDecl { param: Param, expr: Expression },
    VarAssign { name: PtyStr, expr: Expression },
    OpAssign { name: PtyStr, op: BinOp, expr: Expression },
    Block(Box<[Node]>),
    ForLoop { ident: PtyStr, iter: Expression, block: Block },
    WhileLoop { expr: Expression, block: Block },
    IfStatement(IfStatement),
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Param {
    pub ident: PtyStr,
    pub ty: Option<Type>,
}

#[derive(Debug, PartialEq)]
pub enum Block {
    Single(Box<Expression>),
    Multi(Box<[Node]>),
}

impl Block {
    #[must_use]
    pub const fn len(&self) -> usize {
        match self {
            Self::Single(_) => 1,
            Self::Multi(nodes) => nodes.len(),
        }
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Type {
    pub segments: Box<[PtyStr]>,
}

#[derive(Debug, PartialEq)]
pub struct IfStatement {
    pub condition: Expression,
    pub block: Block,
    pub or_else: Option<OrElse>,
}

#[derive(Debug, PartialEq)]
pub enum OrElse {
    Block(Block),
    If(Box<IfStatement>),
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

    Lt,
    LtEq,
    Gt,
    GtEq,
    Eq,
    Ne,

    BitOr,
    Xor,
    BitAnd,
    Shl,
    Shr,

    Add,
    Sub,

    Mul,
    Div,
    Mod,

    Dot,
    PathSep,

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
    Closure { params: Box<[Param]>, block: Block },
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

            Self::Lt => "<",
            Self::LtEq => "<=",
            Self::Gt => ">",
            Self::GtEq => ">=",
            Self::Eq => "==",
            Self::Ne => "!=",

            Self::BitOr => "|",
            Self::Xor => "^",
            Self::BitAnd => "&",
            Self::Shl => "<<",
            Self::Shr => ">>",

            Self::Add => "+",
            Self::Sub => "-",

            Self::Mul => "*",
            Self::Div => "/",
            Self::Mod => "%",

            Self::Dot => ".",
            Self::PathSep => "::",

            Self::RangeInclusive => "..=",
            Self::RangeExclusive => "..",
        }
    }
}
