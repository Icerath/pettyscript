use std::ops::Deref;

use logos::Span;

use crate::lex::TokenKind;

pub type Ident = &'static str;

#[derive(Debug, PartialEq, Clone)]
pub struct Spanned<T> {
    pub inner: T,
    pub span: Span,
}

impl<T> Deref for Spanned<T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Path {
    pub segments: Box<[Ident]>,
}
#[derive(Debug)]
pub enum Stmt {
    Trait(Trait),
    ImplBlock(ImplBlock),
    Struct(Struct),
    Enum(Enum),
    Function(Function),
    ForLoop(ForLoop),
    WhileLoop(WhileLoop),
    IfChain(IfChain),
    Expr(Expr),
    Block(Block),
    Let(Spanned<VarDecl>),
    Const(Spanned<VarDecl>),
    Assign(Assign),
    Continue,
    Break,
    Return(Return),
}

#[derive(Debug)]
pub struct Trait {
    pub name: Ident,
    pub body: Block,
}

#[expect(unused)]
#[derive(Debug)]
pub struct ImplBlock {
    pub generics: Box<[Spanned<Ident>]>,
    pub sig: Spanned<ImplSig>,
    pub body: Block,
}

#[derive(Debug)]
pub enum ImplSig {
    Inherent(Spanned<ExplicitType>),
    Trait([Spanned<ExplicitType>; 2]),
}

#[derive(Debug)]
pub enum Pat {
    Ident(Ident),
    #[expect(unused)]
    Array(Box<[Spanned<Pat>]>),
}

#[derive(Debug, PartialEq)]
pub struct ExplicitType {
    pub ident: Spanned<Ident>,
    pub generics: Box<[Spanned<ExplicitType>]>,
}

impl ExplicitType {
    pub fn is_inferred(&self) -> bool {
        *self.ident == "_"
    }

    pub fn is_self(&self) -> bool {
        *self.ident == "self"
    }
}

#[derive(Debug)]
pub struct Return(pub Option<Expr>);

#[derive(Debug)]
pub struct VarDecl {
    pub pat: Spanned<Pat>,
    pub typ: Option<Spanned<ExplicitType>>,
    pub expr: Option<Expr>,
}

#[derive(Debug)]
pub struct Assign {
    pub root: Spanned<Ident>,
    pub segments: Box<[AssignSegment]>,
    pub expr: Expr,
}

#[derive(Debug)]
pub enum AssignSegment {
    Field(Spanned<Ident>),
    #[expect(unused)]
    Index(Expr),
}

#[derive(Debug)]
pub struct Struct {
    pub ident: Spanned<Ident>,
    pub fields: Box<[Param]>,
}

#[derive(Debug)]
pub struct Enum {
    pub ident: Spanned<Ident>,
    pub variants: Box<[Spanned<Ident>]>,
}

#[expect(unused)]
#[derive(Debug)]
pub struct Generic {
    pub name: Spanned<Ident>,
    pub bounds: Option<Box<[Spanned<Path>]>>,
}

#[derive(Debug)]
pub struct Function {
    pub ident: Spanned<Ident>,
    pub generics: Box<[Generic]>,
    pub params: Box<[Param]>,
    pub ret_type: Option<Spanned<ExplicitType>>,
    pub body: Option<Spanned<Block>>,
}

#[derive(Debug, PartialEq)]
pub struct Param {
    pub ident: Spanned<Ident>,
    pub expl_ty: Spanned<ExplicitType>,
}

#[derive(Debug)]
pub struct Block {
    pub stmts: Box<[Spanned<Stmt>]>,
}

#[derive(Debug)]
pub enum Expr {
    Index { expr: Box<Expr>, index: Box<Expr> },
    FieldAccess { expr: Box<Expr>, field: Spanned<Ident> },
    MethodCall { expr: Box<Expr>, method: Spanned<Ident>, args: Box<[Spanned<Expr>]> },
    Literal(Spanned<Literal>),
    Path(Path),
    Binary { op: BinOp, exprs: Box<[Expr; 2]> },
    Unary { op: UnaryOp, expr: Box<Expr> },
    FnCall { function: Box<Expr>, args: Box<[Spanned<Expr>]> },
    InitStruct { path: Path, fields: Box<[StructInitField]> },
    Array(Box<[Expr]>),
}

#[derive(Debug)]
pub struct StructInitField {
    pub ident: Spanned<Ident>,
    pub expr: Option<Expr>,
}

#[derive(Debug)]
pub enum Literal {
    Bool(bool),
    Int(i64),
    Char(char),
    String(&'static str),
    FString(FString),
    Map(Box<[[Expr; 2]]>),
    Tuple(Box<[Spanned<Expr>]>),
}

#[derive(Debug)]
pub struct FString {
    pub segments: Box<[(Ident, Expr)]>,
    pub remaining: Ident,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Or,
    And,
    Greater,
    Less,
    GreaterEq,
    LessEq,
    Eq,
    Neq,
    Range,
    RangeInclusive,
}

impl TryFrom<TokenKind> for BinOp {
    type Error = ();

    fn try_from(token: TokenKind) -> Result<Self, Self::Error> {
        Ok(match token {
            TokenKind::Plus => Self::Add,
            TokenKind::Minus => Self::Sub,
            TokenKind::Star => Self::Mul,
            TokenKind::Slash => Self::Div,
            TokenKind::Percent => Self::Mod,
            TokenKind::Or => Self::Or,
            TokenKind::And => Self::And,
            TokenKind::RAngle => Self::Greater,
            TokenKind::LAngle => Self::Less,
            TokenKind::RAngleEq => Self::GreaterEq,
            TokenKind::LAngleEq => Self::LessEq,
            TokenKind::EqEq => Self::Eq,
            TokenKind::BangEq => Self::Neq,
            TokenKind::Range => Self::Range,
            TokenKind::RangeInclusive => Self::RangeInclusive,
            _ => return Err(()),
        })
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub enum UnaryOp {
    Not,
    Neg,
    EnumTag,
}

#[derive(Debug)]
pub struct ForLoop {
    pub ident: Spanned<Ident>,
    pub iter: Expr,
    pub body: Spanned<Block>,
}

#[derive(Debug)]
pub struct WhileLoop {
    pub expr: Expr,
    pub body: Spanned<Block>,
}

#[derive(Debug)]
pub struct IfChain {
    pub first: IfStmt,
    pub else_ifs: Box<[IfStmt]>,
    pub r#else: Option<Spanned<Block>>,
}

#[derive(Debug)]
pub struct IfStmt {
    pub condition: Expr,
    pub body: Spanned<Block>,
}
