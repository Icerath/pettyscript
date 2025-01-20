use std::fmt;

use logos::{Lexer, Logos};
use miette::{Context, Error, IntoDiagnostic, LabeledSpan, Result};

use crate::lexer::{Token, TokenKind};

pub enum Stmt {
    Struct(Struct),
    Enum(Enum),
    Function(Function),
    ForLoop(ForLoop),
    IfChain(IfChain),
    Expr(Expr),
    Block(Block),
    Let(VarDecl),
    Const(VarDecl),
}

impl fmt::Debug for Stmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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
            Self::IfChain(if_chain) => fmt::Debug::fmt(if_chain, f),
            Self::Expr(expr) => fmt::Debug::fmt(expr, f),
            Self::ForLoop(for_loop) => fmt::Debug::fmt(for_loop, f),
        }
    }
}

pub struct VarDecl {
    ident: &'static str,
    expr: Option<Expr>,
}

pub struct Struct {
    ident: &'static str,
    fields: Box<[&'static str]>,
}

impl fmt::Debug for Struct {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("struct")
            .field("ident", &format_args!("{}", self.ident))
            .field("fields", &self.fields)
            .finish()
    }
}

pub struct Enum {
    ident: &'static str,
    variants: Box<[&'static str]>,
}

impl fmt::Debug for Enum {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("enum")
            .field("ident", &format_args!("{}", self.ident))
            .field("variants", &self.variants)
            .finish()
    }
}

pub struct Function {
    ident: &'static str,
    params: Box<[&'static str]>,
    block: Block,
}

impl fmt::Debug for Function {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Fn")
            .field("ident", &format_args!("{}", self.ident))
            .field("params", &self.params)
            .field("block", &self.block)
            .finish()
    }
}

pub struct Block {
    stmts: Box<[Stmt]>,
}

impl fmt::Debug for Block {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(&self.stmts).finish()
    }
}

pub enum Expr {
    Literal(Literal),
    Binary { op: BinOp, exprs: Box<[Expr; 2]> },
    Unary { op: UnaryOp, expr: Box<Expr> },
    FnCall { function: Box<Expr>, args: Box<[Expr]> },
    InitStruct { r#struct: Box<Expr>, fields: Box<[StructInitField]> },
}

impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
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

struct StructInitField {
    ident: &'static str,
    expr: Option<Expr>,
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
            Self::Int(int) => write!(f, "Int({int})"),
            Self::String(str) => write!(f, "String({:?})", str),
            Self::Ident(ident) => write!(f, "Ident({ident})"),
        }
    }
}

pub enum Literal {
    Int(i128),
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
    ident: &'static str,
    iter: Expr,
    body: Block,
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

#[derive(Debug)]
pub struct IfChain {
    first: IfStmt,
    else_ifs: Box<[IfStmt]>,
    r#else: Option<Block>,
}

#[derive(Debug)]
pub struct IfStmt {
    condition: Expr,
    body: Block,
}

#[derive(Clone)]
pub struct Parser<'a> {
    lexer: Lexer<'a, Token>,
}

impl<'a> Parser<'a> {
    pub fn new(content: &'a str) -> Self {
        Self { lexer: Token::lexer(content) }
    }

    pub fn parse_root(mut self) -> Result<Box<[Stmt]>> {
        let mut stmts = vec![];
        while self.lexer.clone().next().is_some() {
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
                Token::Semicolon => continue,
                Token::Let => Stmt::Let(self.parse_let_decl()?),
                Token::Const => Stmt::Const(self.parse_const_decl()?),
                Token::Struct => Stmt::Struct(self.parse_struct()?),
                Token::Enum => Stmt::Enum(self.parse_enum()?),
                Token::Fn => Stmt::Function(self.parse_fn()?),
                Token::For => Stmt::ForLoop(self.parse_for_loop()?),
                Token::If => Stmt::IfChain(self.parse_if_chain()?),
                _ => {
                    let expr = self.parse_expr(0)?;
                    self.expect_semicolon()?;
                    Stmt::Expr(expr)
                }
            });
        }
    }

    fn parse_expr(&mut self, precedence: u8) -> Result<Expr> {
        const OPS: &[&[BinOp]] = &[
            &[BinOp::Or],
            &[BinOp::And],
            &[BinOp::Eq, BinOp::Neq, BinOp::Greater, BinOp::Less, BinOp::GreaterEq, BinOp::LessEq],
            &[BinOp::Range, BinOp::RangeInclusive],
            &[BinOp::Add, BinOp::Sub],
            &[BinOp::Mul, BinOp::Div, BinOp::Mod],
        ];

        let Some(&ops) = OPS.get(precedence as usize) else {
            return self.parse_leaf_expr();
        };
        let mut root = self.parse_expr(precedence + 1)?;
        loop {
            let token = self.peek()?;
            let Ok(op) = BinOp::try_from(token.kind()) else { break };
            if !ops.contains(&op) {
                break;
            };
            let _ = self.bump()?;
            let expr = self.parse_expr(precedence + 1)?;
            root = Expr::Binary { op, exprs: Box::new([root, expr]) }
        }
        Ok(root)
    }

    fn parse_leaf_expr(&mut self) -> Result<Expr> {
        let mut expr = self.parse_unary_expr()?;

        while let Token::LParen = self.peek()? {
            let _ = self.bump()?;

            let mut args = vec![];
            while self.peek()? != Token::RParen {
                let expr = self.parse_expr(0)?;
                args.push(expr);
                if self.peek()? == Token::RParen {
                    break;
                }
                self.expect_token(Token::Comma)?;
            }
            let _ = self.bump();
            expr = Expr::FnCall { function: Box::new(expr), args: args.into() };
        }

        if let Token::LBrace = self.peek()? {
            let _ = self.bump()?;

            let mut fields = vec![];
            while self.peek()? != Token::RBrace {
                let ident = self.parse_ident()?;
                if self.peek()? == Token::RBrace {
                    fields.push(StructInitField { ident, expr: None });
                    break;
                }
                let expr = match self.bump()? {
                    Token::Comma => None,
                    Token::Colon => Some(self.parse_expr(0)?),
                    got => {
                        return Err(
                            self.expect_failed(got.kind(), &[TokenKind::Colon, TokenKind::Comma])
                        )
                    }
                };
                fields.push(StructInitField { ident, expr });
            }
            let _ = self.bump();
            expr = Expr::InitStruct { r#struct: Box::new(expr), fields: fields.into() }
        }

        Ok(expr)
    }

    fn parse_unary_expr(&mut self) -> Result<Expr> {
        match self.peek()? {
            Token::Bang => {
                Ok(Expr::Unary { op: UnaryOp::Not, expr: Box::new(self.parse_expr(0)?) })
            }
            _ => self.parse_paren_expr(),
        }
    }

    fn parse_paren_expr(&mut self) -> Result<Expr> {
        if self.peek()? == Token::LParen {
            let _ = self.bump()?;
            let expr = self.parse_expr(0)?;
            self.expect_token(Token::RParen)?;
            return Ok(expr);
        }
        self.parse_literal().map(Expr::Literal)
    }

    fn parse_literal(&mut self) -> Result<Literal> {
        Ok(match self.bump()? {
            Token::Int(int) => Literal::Int(int),
            Token::Ident(ident) => Literal::Ident(ident),
            Token::String(str) => Literal::String(str),
            got => {
                return Err(self.expect_failed(
                    got.kind(),
                    &[TokenKind::Int, TokenKind::String, TokenKind::Ident],
                ));
            }
        })
    }

    fn parse_for_loop(&mut self) -> Result<ForLoop> {
        self.expect_token(Token::For)?;
        let ident = self.parse_ident()?;
        self.expect_token(Token::In)?;
        let iter = self.parse_expr(0)?;
        let body = self.parse_block()?;
        Ok(ForLoop { ident, iter, body })
    }

    fn parse_if_chain(&mut self) -> Result<IfChain> {
        let first = self.parse_if_stmt()?;

        let mut else_ifs = vec![];
        let mut r#else = None;
        while let Token::Else = self.peek()? {
            let _ = self.bump();
            match self.peek()? {
                Token::If => else_ifs.push(self.parse_if_stmt()?),
                Token::LBrace => {
                    r#else = Some(self.parse_block()?);
                    break;
                }
                got => {
                    let _ = self.bump();
                    return Err(self.expect_failed(got.kind(), &[TokenKind::If, TokenKind::LBrace]));
                }
            }
        }
        Ok(IfChain { first, else_ifs: else_ifs.into(), r#else })
    }

    fn parse_if_stmt(&mut self) -> Result<IfStmt> {
        self.expect_token(Token::If)?;
        let condition = self.parse_expr(0)?;
        let body = self.parse_block()?;
        Ok(IfStmt { condition, body })
    }

    fn parse_let_decl(&mut self) -> Result<VarDecl> {
        self.expect_token(Token::Let)?;
        self.parse_var_decl()
    }

    fn parse_const_decl(&mut self) -> Result<VarDecl> {
        self.expect_token(Token::Let)?;
        self.parse_var_decl()
    }

    fn parse_var_decl(&mut self) -> Result<VarDecl> {
        let ident = self.parse_ident()?;
        let expr = match self.bump()? {
            Token::Semicolon => return Ok(VarDecl { ident, expr: None }),
            Token::Eq => self.parse_expr(0)?,
            got => {
                return Err(self.expect_failed(got.kind(), &[TokenKind::Semicolon, TokenKind::Eq]))
            }
        };
        self.expect_semicolon()?;
        Ok(VarDecl { ident, expr: Some(expr) })
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
        let block = self.parse_block()?;
        Ok(Function { ident, params, block })
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

    fn peek(&self) -> Result<Token> {
        self.clone().bump()
    }

    fn peek_span(&mut self) -> Result<std::ops::Range<usize>> {
        let mut copy = self.clone();
        let _ = copy.bump()?;
        Ok(copy.lexer.span())
    }
}
