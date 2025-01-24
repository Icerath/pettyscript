use std::fmt;

use logos::{Lexer, Logos};
use miette::{Context, Error, IntoDiagnostic, LabeledSpan, Result};

use crate::lexer::{Token, TokenKind};

pub fn parse(src: &str) -> Result<Box<[Stmt]>> {
    Parser::new(src).parse_root()
}

pub enum Stmt {
    Struct(Struct),
    Enum(Enum),
    Function(Function),
    ForLoop(ForLoop),
    WhileLoop(WhileLoop),
    IfChain(IfChain),
    Expr(Expr),
    Block(Block),
    Let(VarDecl),
    Const(VarDecl),
    Assign(Assign),
    Continue,
    Break,
    Return(Return),
}

impl fmt::Debug for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Continue => f.debug_struct("Continue").finish(),
            Self::Break => f.debug_struct("Break").finish(),
            Self::Return(r#return) => fmt::Debug::fmt(r#return, f),
            Self::Assign(Assign { root, segments, expr }) => f
                .debug_struct("Assign")
                .field("root", root)
                .field("segments", &segments)
                .field("expr", expr)
                .finish(),
            Self::Let(var) => {
                f.debug_struct("let").field("ident", &var.ident).field("expr", &var.expr).finish()
            }
            Self::Const(var) => {
                f.debug_struct("const").field("ident", &var.ident).field("expr", &var.expr).finish()
            }
            Self::Struct(r#struct) => fmt::Debug::fmt(r#struct, f),
            Self::Enum(r#enum) => fmt::Debug::fmt(r#enum, f),
            Self::Block(block) => fmt::Debug::fmt(block, f),
            Self::Function(fun) => fmt::Debug::fmt(fun, f),
            Self::WhileLoop(while_loop) => fmt::Debug::fmt(while_loop, f),
            Self::IfChain(if_chain) => fmt::Debug::fmt(if_chain, f),
            Self::Expr(expr) => fmt::Debug::fmt(expr, f),
            Self::ForLoop(for_loop) => fmt::Debug::fmt(for_loop, f),
        }
    }
}

#[derive(Debug)]
pub struct Return(pub Option<Expr>);

pub struct VarDecl {
    pub ident: &'static str,
    pub expr: Option<Expr>,
}

pub struct Assign {
    pub root: &'static str,
    pub segments: Box<[AssignSegment]>,
    pub expr: Expr,
}

#[derive(Debug)]
pub enum AssignSegment {
    Field(&'static str),
    #[expect(unused)]
    Index(Expr),
}

pub struct Struct {
    pub ident: &'static str,
    pub fields: Box<[&'static str]>,
}

impl fmt::Debug for Struct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Struct")
            .field("ident", &format_args!("{}", self.ident))
            .field("fields", &self.fields)
            .finish()
    }
}

pub struct Enum {
    pub ident: &'static str,
    pub variants: Box<[&'static str]>,
}

impl fmt::Debug for Enum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Enum")
            .field("ident", &format_args!("{}", self.ident))
            .field("variants", &self.variants)
            .finish()
    }
}

pub struct Function {
    pub ident: &'static str,
    pub params: Box<[&'static str]>,
    pub body: Block,
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Fn")
            .field("ident", &format_args!("{}", self.ident))
            .field("params", &self.params)
            .field("body", &self.body)
            .finish()
    }
}

pub struct Block {
    pub stmts: Box<[Stmt]>,
}

impl fmt::Debug for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(&self.stmts).finish()
    }
}

pub enum Expr {
    Index { expr: Box<Expr>, index: Box<Expr> },
    FieldAccess { expr: Box<Expr>, field: &'static str },
    Literal(Literal),
    Binary { op: BinOp, exprs: Box<[Expr; 2]> },
    Unary { op: UnaryOp, expr: Box<Expr> },
    FnCall { function: Box<Expr>, args: Box<[Expr]> },
    InitStruct { r#struct: Box<Expr>, fields: Box<[StructInitField]> },
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Index { expr, index } => {
                f.debug_struct("Index").field("expr", expr).field("index", index).finish()
            }
            Self::FieldAccess { expr, field } => f
                .debug_struct("field_access")
                .field("expr", expr)
                .field("field", &format_args!("{}", field))
                .finish(),
            Self::InitStruct { r#struct, fields } => f
                .debug_struct("InitStruct")
                .field("struct", r#struct)
                .field("fields", fields)
                .finish(),
            Self::Literal(literal) => fmt::Debug::fmt(literal, f),
            Self::Binary { op, exprs } => f
                .debug_struct("BinaryExpr")
                .field("lhs", &exprs[0])
                .field("op", op)
                .field("rhs", &exprs[1])
                .finish(),
            Self::Unary { op, expr } => {
                f.debug_struct("UnaryExpr").field("op", op).field("expr", expr).finish()
            }
            Self::FnCall { function, args } => {
                f.debug_struct("FnCall").field("function", function).field("args", args).finish()
            }
        }
    }
}

pub struct StructInitField {
    pub ident: &'static str,
    pub expr: Option<Expr>,
}

impl fmt::Debug for StructInitField {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("InitField")
            .field("ident", &format_args!("{}", self.ident))
            .field("expr", &self.expr)
            .finish()
    }
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(bool) => write!(f, "Bool({bool})"),
            Self::Int(int) => write!(f, "Int({int})"),
            Self::Char(char) => write!(f, "Char({char:?})"),
            Self::String(str) => write!(f, "String({str:?})"),
            Self::Ident(ident) => write!(f, "Ident({ident})"),
        }
    }
}

pub enum Literal {
    Bool(bool),
    Int(i128),
    Char(char),
    String(&'static str),
    Ident(&'static str),
}

#[derive(Debug, PartialEq)]
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

#[derive(Debug)]
pub enum UnaryOp {
    Not,
}

pub struct ForLoop {
    pub ident: &'static str,
    pub iter: Expr,
    pub body: Block,
}

impl fmt::Debug for ForLoop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ForLoop")
            .field("ident", &format_args!("{}", self.ident))
            .field("iter", &self.iter)
            .field("body", &self.body)
            .finish()
    }
}

pub struct WhileLoop {
    pub expr: Expr,
    pub body: Block,
}

impl fmt::Debug for WhileLoop {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("WhileLoop").field("expr", &self.expr).field("body", &self.body).finish()
    }
}

#[derive(Debug)]
pub struct IfChain {
    pub first: IfStmt,
    pub else_ifs: Box<[IfStmt]>,
    pub r#else: Option<Block>,
}

#[derive(Debug)]
pub struct IfStmt {
    pub condition: Expr,
    pub body: Block,
}

#[derive(Clone)]
struct Parser<'a> {
    lexer: Lexer<'a, Token>,
}

impl<'a> Parser<'a> {
    fn new(content: &'a str) -> Self {
        Self { lexer: Token::lexer(content) }
    }

    fn parse_root(mut self) -> Result<Box<[Stmt]>> {
        let mut stmts = vec![];
        while self.lexer.clone().next().is_some() {
            if self.peek()? == Token::Semicolon {
                self.skip();
                continue;
            }
            stmts.push(self.parse_stmt()?);
        }
        Ok(stmts.into_boxed_slice())
    }

    fn src(&self) -> String {
        self.lexer.source().to_owned()
    }

    fn parse_stmt(&mut self) -> Result<Stmt> {
        loop {
            break Ok(match self.peek()? {
                Token::Semicolon => {
                    self.skip();
                    continue;
                }
                Token::Return => Stmt::Return(self.parse_return_stmt()?),
                Token::Break => {
                    self.skip();
                    self.expect_semicolon()?;
                    Stmt::Break
                }
                Token::Continue => {
                    self.skip();
                    self.expect_semicolon()?;
                    Stmt::Continue
                }
                Token::Let => Stmt::Let(self.parse_let_decl()?),
                Token::Const => Stmt::Const(self.parse_const_decl()?),
                Token::Struct => Stmt::Struct(self.parse_struct()?),
                Token::Enum => Stmt::Enum(self.parse_enum()?),
                Token::Fn => Stmt::Function(self.parse_fn()?),
                Token::For => Stmt::ForLoop(self.parse_for_loop()?),
                Token::While => Stmt::WhileLoop(self.parse_while_loop()?),
                Token::If => Stmt::IfChain(self.parse_if_chain()?),
                Token::LBrace => Stmt::Block(self.parse_block()?),
                Token::Ident(_) => {
                    let prev = self.clone();
                    let Ok(assign) = self.parse_assignment() else {
                        *self = prev;
                        let expr = self.parse_root_expr()?;
                        self.expect_semicolon()?;
                        break Ok(Stmt::Expr(expr));
                    };
                    Stmt::Assign(assign)
                }
                _ => {
                    let expr = self.parse_root_expr()?;
                    self.expect_semicolon()?;
                    Stmt::Expr(expr)
                }
            });
        }
    }

    fn parse_root_expr(&mut self) -> Result<Expr> {
        self.parse_expr(0, true)
    }

    fn parse_expr(&mut self, precedence: u8, allow_struct_init: bool) -> Result<Expr> {
        const OPS: &[&[BinOp]] = &[
            &[BinOp::Or],
            &[BinOp::And],
            &[BinOp::Eq, BinOp::Neq, BinOp::Greater, BinOp::Less, BinOp::GreaterEq, BinOp::LessEq],
            &[BinOp::Range, BinOp::RangeInclusive],
            &[BinOp::Add, BinOp::Sub],
            &[BinOp::Mul, BinOp::Div, BinOp::Mod],
        ];

        let Some(&ops) = OPS.get(precedence as usize) else {
            return self.parse_leaf_expr(allow_struct_init);
        };
        let mut root = self.parse_expr(precedence + 1, allow_struct_init)?;
        loop {
            let token = self.peek()?;
            let Ok(op) = BinOp::try_from(token.kind()) else { break };
            if !ops.contains(&op) {
                break;
            };
            self.skip();
            let expr = self.parse_expr(precedence + 1, allow_struct_init)?;
            root = Expr::Binary { op, exprs: Box::new([root, expr]) }
        }
        Ok(root)
    }

    fn parse_leaf_expr(&mut self, allow_struct_init: bool) -> Result<Expr> {
        let mut expr = self.parse_unary_expr(allow_struct_init)?;

        loop {
            match self.peek()? {
                Token::LParen => {
                    self.skip();
                    let mut args = vec![];
                    while self.peek()? != Token::RParen {
                        let expr = self.parse_root_expr()?;
                        args.push(expr);
                        if self.peek()? == Token::RParen {
                            break;
                        }
                        self.expect_token(Token::Comma)?;
                    }
                    self.skip();
                    expr = Expr::FnCall { function: Box::new(expr), args: args.into() };
                }
                Token::Dot => {
                    self.skip();
                    let field = self.parse_ident()?;
                    expr = Expr::FieldAccess { expr: Box::new(expr), field };
                }
                Token::LBracket => {
                    self.skip();
                    let index = self.parse_root_expr()?;
                    self.expect_token(Token::RBracket)?;
                    expr = Expr::Index { expr: Box::new(expr), index: Box::new(index) };
                }
                _ => break,
            }
        }
        if !allow_struct_init {
            return Ok(expr);
        }

        if let Token::LBrace = self.peek()? {
            self.skip();
            let mut fields = vec![];
            while self.peek()? != Token::RBrace {
                let ident = self.parse_ident()?;
                if self.peek()? == Token::RBrace {
                    fields.push(StructInitField { ident, expr: None });
                    break;
                }
                let expr = match self.bump()? {
                    Token::Comma => None,
                    Token::Colon => {
                        let expr = self.parse_root_expr()?;
                        match self.peek()? {
                            Token::Comma => self.skip(),
                            Token::RBrace => {}
                            got => {
                                // TODO: Better error placement
                                self.skip();
                                return Err(self.expect_failed(
                                    got.kind(),
                                    &[TokenKind::Comma, TokenKind::LBrace],
                                ));
                            }
                        }
                        Some(expr)
                    }
                    got => {
                        return Err(
                            self.expect_failed(got.kind(), &[TokenKind::Colon, TokenKind::Comma])
                        )
                    }
                };
                fields.push(StructInitField { ident, expr });
            }
            self.skip();
            expr = Expr::InitStruct { r#struct: Box::new(expr), fields: fields.into() }
        }

        Ok(expr)
    }

    fn parse_unary_expr(&mut self, allow_struct_init: bool) -> Result<Expr> {
        match self.peek()? {
            Token::Bang => Ok(Expr::Unary {
                op: UnaryOp::Not,
                expr: Box::new(self.parse_expr(0, allow_struct_init)?),
            }),
            _ => self.parse_paren_expr(),
        }
    }

    fn parse_paren_expr(&mut self) -> Result<Expr> {
        if self.peek()? == Token::LParen {
            self.skip();
            let expr = self.parse_root_expr()?;
            self.expect_token(Token::RParen)?;
            return Ok(expr);
        }
        self.parse_literal().map(Expr::Literal)
    }

    fn parse_literal(&mut self) -> Result<Literal> {
        Ok(match self.bump()? {
            Token::Int(int) => Literal::Int(int),
            Token::Char(char) => Literal::Char(char),
            Token::Ident(ident) => Literal::Ident(ident),
            Token::String(str) => Literal::String(str),
            Token::True => Literal::Bool(true),
            Token::False => Literal::Bool(false),
            got => {
                return Err(self.expect_failed(
                    got.kind(),
                    &[TokenKind::Int, TokenKind::Char, TokenKind::String, TokenKind::Ident],
                ));
            }
        })
    }

    fn parse_for_loop(&mut self) -> Result<ForLoop> {
        self.expect_token(Token::For)?;
        let ident = self.parse_ident()?;
        self.expect_token(Token::In)?;
        let iter = self.parse_expr(0, false)?;
        let body = self.parse_block()?;
        Ok(ForLoop { ident, iter, body })
    }

    fn parse_while_loop(&mut self) -> Result<WhileLoop> {
        self.expect_token(Token::While)?;
        let expr = self.parse_expr(0, false)?;
        let body = self.parse_block()?;
        Ok(WhileLoop { expr, body })
    }

    fn parse_if_chain(&mut self) -> Result<IfChain> {
        let first = self.parse_if_stmt()?;

        let mut else_ifs = vec![];
        let mut r#else = None;
        while let Token::Else = self.peek()? {
            self.skip();
            match self.peek()? {
                Token::If => else_ifs.push(self.parse_if_stmt()?),
                Token::LBrace => {
                    r#else = Some(self.parse_block()?);
                    break;
                }
                got => {
                    self.skip();
                    return Err(self.expect_failed(got.kind(), &[TokenKind::If, TokenKind::LBrace]));
                }
            }
        }
        Ok(IfChain { first, else_ifs: else_ifs.into(), r#else })
    }

    fn parse_if_stmt(&mut self) -> Result<IfStmt> {
        self.expect_token(Token::If)?;
        let condition = self.parse_expr(0, false)?;
        let body = self.parse_block()?;
        Ok(IfStmt { condition, body })
    }

    fn parse_return_stmt(&mut self) -> Result<Return> {
        self.expect_token(Token::Return)?;
        let expr =
            if self.peek()? == Token::Semicolon { None } else { Some(self.parse_root_expr()?) };
        self.expect_semicolon()?;
        Ok(Return(expr))
    }

    fn parse_let_decl(&mut self) -> Result<VarDecl> {
        self.expect_token(Token::Let)?;
        self.parse_var_decl()
    }

    fn parse_const_decl(&mut self) -> Result<VarDecl> {
        self.expect_token(Token::Const)?;
        self.parse_var_decl()
    }

    fn parse_var_decl(&mut self) -> Result<VarDecl> {
        let ident = self.parse_ident()?;
        let expr = match self.bump()? {
            Token::Semicolon => return Ok(VarDecl { ident, expr: None }),
            Token::Eq => self.parse_root_expr()?,
            got => {
                return Err(self.expect_failed(got.kind(), &[TokenKind::Semicolon, TokenKind::Eq]))
            }
        };
        self.expect_semicolon()?;
        Ok(VarDecl { ident, expr: Some(expr) })
    }

    fn parse_assignment(&mut self) -> Result<Assign> {
        let root = self.parse_ident()?;
        let mut segments = vec![];
        loop {
            match self.bump()? {
                Token::Eq => break,
                Token::Dot => {
                    let field = self.parse_ident()?;
                    segments.push(AssignSegment::Field(field));
                }
                Token::LBracket => {
                    let index = self.parse_root_expr()?;
                    self.expect_token(Token::RBracket)?;
                    segments.push(AssignSegment::Index(index));
                }
                _ => return Err(miette::miette!("")),
            }
        }
        let expr = self.parse_root_expr()?;
        self.expect_semicolon()?;
        Ok(Assign { root, segments: segments.into(), expr })
    }

    fn parse_struct(&mut self) -> Result<Struct> {
        self.expect_token(Token::Struct)?;
        let ident = self.parse_ident()?;
        self.expect_token(Token::LBrace)?;
        let fields = self.parse_separated_idents(TokenKind::RBrace)?;
        self.expect_token(Token::RBrace)?;
        Ok(Struct { ident, fields })
    }

    fn parse_enum(&mut self) -> Result<Enum> {
        self.expect_token(Token::Enum)?;
        let ident = self.parse_ident()?;
        self.expect_token(Token::LBrace)?;
        let variants = self.parse_separated_idents(TokenKind::RBrace)?;
        self.expect_token(Token::RBrace)?;
        Ok(Enum { ident, variants })
    }

    fn parse_fn(&mut self) -> Result<Function> {
        self.expect_token(Token::Fn)?;
        let ident = self.parse_ident()?;
        self.expect_token(Token::LParen)?;
        let params = self.parse_separated_idents(TokenKind::RParen)?;
        self.expect_token(Token::RParen)?;
        let body = self.parse_block()?;
        Ok(Function { ident, params, body })
    }

    fn parse_separated_idents(&mut self, terminator: TokenKind) -> Result<Box<[&'static str]>> {
        let mut params = vec![];
        while self.peek()?.kind() != terminator {
            let ident = self.parse_ident()?;
            params.push(ident);
            if self.peek()?.kind() == terminator {
                break;
            }
            self.expect_token(Token::Comma)?;
        }
        Ok(params.into())
    }

    fn parse_block(&mut self) -> Result<Block> {
        self.expect_token(Token::LBrace)?;
        let mut stmts = vec![];
        while self.peek()? != Token::RBrace {
            if self.peek()? == Token::Semicolon {
                self.skip();
                continue;
            }
            stmts.push(self.parse_stmt()?);
        }
        let stmts = stmts.into_boxed_slice();
        self.expect_token(Token::RBrace)?;
        Ok(Block { stmts })
    }

    fn parse_ident(&mut self) -> Result<&'static str> {
        let Token::Ident(ident) = self.expect_token(TokenKind::Ident)? else { unreachable!() };
        Ok(ident)
    }

    fn expect_token(&mut self, expected: impl Into<TokenKind>) -> Result<Token> {
        self.expect_any(&[expected.into()])
    }

    /// Semicolons specifically should not show as expected over the next token.
    fn expect_semicolon(&mut self) -> Result<()> {
        let span = self.lexer.span().end..self.lexer.span().end;
        if let Token::Semicolon = self.bump()? {
            return Ok(());
        }
        let span = LabeledSpan::at(span, "expected ';' here");
        Err(miette::miette!(labels = vec![span], "Missing ';'").with_source_code(self.src()))
    }

    fn expect_any(&mut self, one_of: &[TokenKind]) -> Result<Token> {
        match self.bump()? {
            got if one_of.contains(&got.kind()) => Ok(got),
            got => Err(self.expect_failed(got.kind(), one_of)),
        }
    }

    fn expect_failed(&self, got: TokenKind, one_of: &[TokenKind]) -> Error {
        debug_assert_ne!(one_of.len(), 0);
        let expect_msg = {
            let prefix = if one_of.len() > 1 { "one of " } else { "" };
            let mut reprs = vec![];
            reprs.extend(one_of.iter().map(|kind| format!("'{}'", kind.repr())));
            prefix.to_string() + &reprs.join("|")
        };
        let span = LabeledSpan::at(self.lexer.span(), format!("expected {expect_msg} here"));
        miette::miette!(labels = vec![span], "Expected: {expect_msg}, Got: '{got}'")
            .with_source_code(self.src())
    }

    fn bump(&mut self) -> Result<Token> {
        self.lexer.next().context("Lexer Error")?.into_diagnostic()
    }

    fn skip(&mut self) {
        #[cfg(debug_assertions)]
        let _ = self.lexer.next().unwrap().unwrap();
        #[cfg(not(debug_assertions))]
        let _ = self.lexer.next();
    }

    fn peek(&self) -> Result<Token> {
        self.clone().bump()
    }
}
