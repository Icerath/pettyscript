use std::ops::{Deref, DerefMut};

use logos::{Logos, Span};
use miette::{Error, LabeledSpan, Result};

use crate::{
    intern::intern,
    lexer::{Token, TokenKind},
};

pub fn parse(src: &str) -> Result<Box<[Spanned<Stmt>]>> {
    Parser::new(src).parse_root()
}

pub type Ident = &'static str;
type Lexer<'a> = logos::Lexer<'a, Token>;

#[derive(Debug, PartialEq, Eq, Hash)]
pub struct Path {
    pub segments: Box<[Ident]>,
}

impl Path {
    pub fn one(ident: &'static str) -> Self {
        Self { segments: Box::new([ident]) }
    }
}

#[derive(Debug)]
pub enum Stmt {
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
    #[expect(unused)]
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

#[derive(Debug)]
pub struct Function {
    pub ident: Spanned<Ident>,
    #[expect(unused)]
    pub generics: Box<[Spanned<Ident>]>,
    pub params: Box<[Param]>,
    pub ret_type: Option<Spanned<ExplicitType>>,
    pub body: Spanned<Block>,
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

#[derive(Clone)]
struct Parser<'a> {
    lexer: Lexer<'a>,
}

impl<'a> Parser<'a> {
    fn new(content: &'a str) -> Self {
        Self { lexer: Token::lexer(content) }
    }

    fn parse<T: Parse>(&mut self) -> Result<T> {
        T::parse(self)
    }

    fn parse_root(mut self) -> Result<Box<[Spanned<Stmt>]>> {
        let mut stmts = vec![];
        while self.lexer.clone().next().is_some() {
            if self.peek()? == Token::Semicolon {
                self.skip();
                continue;
            }
            stmts.push(self.parse()?);
        }
        Ok(stmts.into_boxed_slice())
    }

    fn src(&self) -> String {
        self.lexer.source().to_owned()
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

    fn parse_separated<T>(&mut self, sep: TokenKind, terminator: TokenKind) -> Result<Box<[T]>>
    where
        T: Parse,
    {
        let mut args = vec![];
        while self.peek()?.kind() != terminator {
            let expr = self.parse()?;
            args.push(expr);
            if self.peek()?.kind() == terminator {
                break;
            }
            self.expect_token(sep)?;
        }
        self.skip();
        Ok(args.into())
    }

    fn parse_leaf_expr(&mut self, allow_struct_init: bool) -> Result<Expr> {
        let mut expr = self.parse_unary_expr(allow_struct_init)?;

        loop {
            match self.peek()? {
                Token::LParen => {
                    self.skip();
                    let args = self.parse_separated(TokenKind::Comma, TokenKind::RParen)?;
                    expr = Expr::FnCall { function: Box::new(expr), args };
                }
                Token::Dot => 'block: {
                    self.skip();
                    let field = self.parse()?;
                    if self.peek()? != Token::LParen {
                        expr = Expr::FieldAccess { expr: Box::new(expr), field };
                        break 'block;
                    }
                    self.skip();
                    let args = self.parse_separated(TokenKind::Comma, TokenKind::RParen)?;
                    expr = Expr::MethodCall { expr: Box::new(expr), method: field, args }
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
        let Token::LBrace = self.peek()? else { return Ok(expr) };
        let Expr::Path(path) = expr else {
            // This is actually an error, but it is better handled later.
            return Ok(expr);
        };
        self.parse_struct_init(path)
    }

    fn parse_struct_init(&mut self, path: Path) -> Result<Expr> {
        self.expect_token(Token::LBrace)?;
        let mut fields = vec![];
        while self.peek()? != Token::RBrace {
            let ident = self.parse()?;
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
                            return Err(self.expect_failed(got.kind(), &[
                                TokenKind::Comma,
                                TokenKind::LBrace,
                            ]));
                        }
                    }
                    Some(expr)
                }
                got => {
                    return Err(
                        self.expect_failed(got.kind(), &[TokenKind::Colon, TokenKind::Comma])
                    );
                }
            };
            fields.push(StructInitField { ident, expr });
        }
        self.skip();
        Ok(Expr::InitStruct { path, fields: fields.into() })
    }

    fn parse_unary_expr(&mut self, allow_struct_init: bool) -> Result<Expr> {
        match self.peek()? {
            Token::Minus => {
                self.skip();
                Ok(Expr::Unary {
                    op: UnaryOp::Neg,
                    expr: Box::new(self.parse_expr(0, allow_struct_init)?),
                })
            }
            Token::Bang => {
                self.skip();
                Ok(Expr::Unary {
                    op: UnaryOp::Not,
                    expr: Box::new(self.parse_expr(0, allow_struct_init)?),
                })
            }
            Token::LBracket => self.parse_list_expr().map(Expr::Array),
            _ => self.parse_paren_expr(),
        }
    }

    fn parse_list_expr(&mut self) -> Result<Box<[Expr]>> {
        self.expect_token(Token::LBracket)?;

        let mut values = vec![];
        while self.peek()? != Token::RBracket {
            let expr = self.parse_root_expr()?;
            values.push(expr);
            if self.peek()? == Token::Comma {
                self.skip();
            }
        }
        self.skip();
        Ok(values.into())
    }

    fn parse_paren_expr(&mut self) -> Result<Expr> {
        if self.peek()? == Token::LParen {
            self.skip();
            let expr = self.parse_root_expr()?;
            self.expect_token(Token::RParen)?;
            return Ok(expr);
        }
        if self.peek()?.kind() == TokenKind::Ident {
            return self.parse().map(Expr::Path);
        }
        Spanned::<Literal>::parse(self).map(Expr::Literal)
    }

    fn parse_map_literal(&mut self) -> Result<Literal> {
        // We expect hash too, but it's already parsed by `parse_literal`
        self.expect_token(Token::LBrace)?;
        let mut entries = vec![];
        while self.peek()? != Token::RBrace {
            let key = self.parse_root_expr()?;
            self.expect_token(Token::Colon)?;
            let value = self.parse_root_expr()?;
            entries.push([key, value]);
            match self.peek()? {
                Token::RBrace => break,
                Token::Comma => self.skip(),
                got => {
                    return Err(
                        self.expect_failed(got.kind(), &[TokenKind::RBrace, TokenKind::Comma])
                    );
                }
            }
        }
        self.skip();
        Ok(Literal::Map(entries.into()))
    }

    fn parse_tuple_literal(&mut self) -> Result<Literal> {
        self.expect_token(Token::LBracket)?;
        let exprs = self.parse_separated(TokenKind::Comma, TokenKind::RBracket)?;
        Ok(Literal::Tuple(exprs))
    }

    fn parse_fstring(str: &str) -> Result<FString> {
        // FIXME: Better error and unicode.
        let mut i = 0;
        let mut section_start = 0;
        let mut segments = vec![];
        while i < str.len() {
            if str.as_bytes()[i] == b'{' {
                let mut end = i;
                {
                    let mut lbraces = 1;
                    while lbraces != 0 {
                        end += 1;
                        match str.as_bytes()[end] as char {
                            '{' => lbraces += 1,
                            '}' => lbraces -= 1,
                            _ => {}
                        }
                    }
                }
                let expr_str = &str[1..][i..end];
                // FIXME: Handle EOF correctly to avoid this.
                let expr = Parser::new(&(expr_str.to_string() + ";")).parse_root_expr()?;
                let section = intern(&str[section_start..i]);
                i = end;
                section_start = i + 1;
                segments.push((section, expr));
            }
            i += 1;
        }
        let remaining = intern(&str[section_start..i]);
        Ok(FString { segments: segments.into(), remaining })
    }

    fn parse_if_stmt(&mut self) -> Result<IfStmt> {
        self.expect_token(Token::If)?;
        let condition = self.parse_expr(0, false)?;
        let body = self.parse()?;
        Ok(IfStmt { condition, body })
    }

    fn parse_let_decl(&mut self) -> Result<Spanned<VarDecl>> {
        self.expect_token(Token::Let)?;
        self.parse_var_decl()
    }

    fn parse_const_decl(&mut self) -> Result<Spanned<VarDecl>> {
        self.expect_token(Token::Const)?;
        self.parse_var_decl()
    }

    fn parse_var_decl(&mut self) -> Result<Spanned<VarDecl>> {
        let start = self.lexer.span().start;
        let pat = self.parse()?;
        let mut typ = None;
        if self.peek()? == Token::Colon {
            self.skip();
            typ = Some(self.parse()?);
        }
        let expr = match self.bump()? {
            Token::Semicolon => {
                return Ok(Spanned {
                    inner: VarDecl { pat, typ, expr: None },
                    span: start..self.lexer.span().end,
                });
            }
            Token::Eq => self.parse_root_expr()?,
            got => {
                return Err(self.expect_failed(got.kind(), &[TokenKind::Semicolon, TokenKind::Eq]));
            }
        };
        self.expect_semicolon()?;
        Ok(Spanned {
            inner: VarDecl { pat, typ, expr: Some(expr) },
            span: start..self.lexer.span().end,
        })
    }

    fn parse_assignment(&mut self) -> Result<Assign> {
        let root = self.parse()?;
        let mut segments = vec![];
        loop {
            match self.bump()? {
                Token::Eq => break,
                Token::Dot => segments.push(AssignSegment::Field(self.parse()?)),
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
        let span = self.lexer.span();
        match self.lexer.next() {
            Some(Ok(tok)) => Ok(tok),
            Some(Err(())) => {
                let span = LabeledSpan::at_offset(span.end, "here");
                Err(miette::miette!(labels = vec![span], "Lexer Error")
                    .with_source_code(self.src()))
            }
            None => {
                let span = LabeledSpan::at(span, "here");
                Err(miette::miette!(labels = vec![span], "Lexer Error")
                    .with_source_code(self.src()))
            }
        }
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

impl<T> DerefMut for Spanned<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.inner
    }
}

trait Parse: Sized {
    fn parse(stream: &mut Parser) -> Result<Self>;
}

impl<T: Parse> Parse for Spanned<T> {
    fn parse(stream: &mut Parser) -> Result<Self> {
        let mut copy = stream.lexer.clone();
        _ = copy.next();
        let start = copy.span().start;
        let inner = T::parse(stream)?;
        let span = start..stream.lexer.span().end;
        Ok(Spanned { inner, span })
    }
}

impl Parse for Stmt {
    fn parse(stream: &mut Parser) -> Result<Self> {
        loop {
            break Ok(match stream.peek()? {
                Token::Semicolon => {
                    stream.skip();
                    continue;
                }
                Token::Return => Stmt::Return(Return::parse(stream)?),
                Token::Break => {
                    stream.skip();
                    stream.expect_semicolon()?;
                    Stmt::Break
                }
                Token::Continue => {
                    stream.skip();
                    stream.expect_semicolon()?;
                    Stmt::Continue
                }
                Token::Impl => Stmt::ImplBlock(ImplBlock::parse(stream)?),
                Token::Let => Stmt::Let(stream.parse_let_decl()?),
                Token::Const => Stmt::Const(stream.parse_const_decl()?),
                Token::Struct => Stmt::Struct(Struct::parse(stream)?),
                Token::Enum => Stmt::Enum(Enum::parse(stream)?),
                Token::Fn => Stmt::Function(Function::parse(stream)?),
                Token::For => Stmt::ForLoop(ForLoop::parse(stream)?),
                Token::While => Stmt::WhileLoop(WhileLoop::parse(stream)?),
                Token::If => Stmt::IfChain(IfChain::parse(stream)?),
                Token::LBrace => Stmt::Block(Block::parse(stream)?),
                Token::Ident(_) => {
                    let prev = stream.clone();
                    let Ok(assign) = stream.parse_assignment() else {
                        *stream = prev;
                        let expr = stream.parse_root_expr()?;
                        stream.expect_semicolon()?;
                        break Ok(Stmt::Expr(expr));
                    };
                    Stmt::Assign(assign)
                }
                _ => {
                    let expr = stream.parse_root_expr()?;
                    stream.expect_semicolon()?;
                    Stmt::Expr(expr)
                }
            });
        }
    }
}

impl Parse for Return {
    fn parse(stream: &mut Parser) -> Result<Self> {
        stream.expect_token(Token::Return)?;
        let expr =
            if stream.peek()? == Token::Semicolon { None } else { Some(stream.parse_root_expr()?) };
        stream.expect_semicolon()?;
        Ok(Return(expr))
    }
}

impl Parse for IfChain {
    fn parse(stream: &mut Parser) -> Result<Self> {
        let first = stream.parse_if_stmt()?;

        let mut else_ifs = vec![];
        let mut r#else = None;
        while let Token::Else = stream.peek()? {
            stream.skip();
            match stream.peek()? {
                Token::If => else_ifs.push(stream.parse_if_stmt()?),
                Token::LBrace => {
                    r#else = Some(stream.parse()?);
                    break;
                }
                got => {
                    stream.skip();
                    return Err(
                        stream.expect_failed(got.kind(), &[TokenKind::If, TokenKind::LBrace])
                    );
                }
            }
        }
        Ok(IfChain { first, else_ifs: else_ifs.into(), r#else })
    }
}

impl Parse for Function {
    fn parse(stream: &mut Parser) -> Result<Self> {
        stream.expect_token(Token::Fn)?;
        let ident = stream.parse()?;

        let mut generics: Box<[_]> = Box::new([]);
        if stream.peek()? == Token::LBracket {
            stream.skip();
            generics = stream.parse_separated(TokenKind::Comma, TokenKind::RBracket)?;
        }

        stream.expect_token(Token::LParen)?;
        let params = stream.parse_separated(TokenKind::Comma, TokenKind::RParen)?;

        let mut ret_type = None;
        if stream.peek()? == Token::ThinArrow {
            stream.skip();
            ret_type = Some(stream.parse()?);
        }

        let body = stream.parse()?;
        Ok(Function { ident, generics, params, ret_type, body })
    }
}

impl Parse for WhileLoop {
    fn parse(stream: &mut Parser) -> Result<Self> {
        stream.expect_token(Token::While)?;
        let expr = stream.parse_expr(0, false)?;
        let body = stream.parse()?;
        Ok(WhileLoop { expr, body })
    }
}

impl Parse for ForLoop {
    fn parse(stream: &mut Parser) -> Result<Self> {
        stream.expect_token(Token::For)?;
        let ident = stream.parse()?;
        stream.expect_token(Token::In)?;
        let iter = stream.parse_expr(0, false)?;
        let body = stream.parse()?;
        Ok(ForLoop { ident, iter, body })
    }
}

impl Parse for Struct {
    fn parse(stream: &mut Parser) -> Result<Self> {
        stream.expect_token(Token::Struct)?;
        let ident = stream.parse()?;
        stream.expect_token(Token::LBrace)?;
        let fields = stream.parse_separated(TokenKind::Comma, TokenKind::RBrace)?;
        Ok(Struct { ident, fields })
    }
}

impl Parse for Enum {
    fn parse(stream: &mut Parser) -> Result<Self> {
        stream.expect_token(Token::Enum)?;
        let ident = stream.parse()?;
        stream.expect_token(Token::LBrace)?;
        let variants = stream.parse_separated(TokenKind::Comma, TokenKind::RBrace)?;
        Ok(Enum { ident, variants })
    }
}

impl Parse for Block {
    fn parse(stream: &mut Parser) -> Result<Self> {
        stream.expect_token(Token::LBrace)?;
        let mut stmts = vec![];
        while stream.peek()? != Token::RBrace {
            if stream.peek()? == Token::Semicolon {
                stream.skip();
                continue;
            }
            stmts.push(stream.parse()?);
        }
        let stmts = stmts.into_boxed_slice();
        stream.expect_token(Token::RBrace)?;
        Ok(Block { stmts })
    }
}

impl Parse for Ident {
    fn parse(stream: &mut Parser) -> Result<Self> {
        match stream.expect_token(TokenKind::Ident)? {
            Token::Ident(ident) => Ok(ident),
            _ => unreachable!(),
        }
    }
}

impl Parse for ExplicitType {
    fn parse(stream: &mut Parser) -> Result<Self> {
        let ident = stream.parse()?;
        if stream.peek()? != Token::LBracket {
            return Ok(ExplicitType { ident, generics: [].into() });
        }
        stream.skip();
        let mut generics = vec![];
        while stream.peek()?.kind() != TokenKind::RBracket {
            generics.push(stream.parse()?);
            if stream.peek()?.kind() == TokenKind::RBracket {
                break;
            }
            stream.expect_token(Token::Comma)?;
        }
        stream.skip();
        Ok(ExplicitType { ident, generics: generics.into() })
    }
}

impl Parse for Literal {
    fn parse(stream: &mut Parser) -> Result<Self> {
        Ok(match stream.bump()? {
            Token::Int(int) => Literal::Int(int),
            Token::Char(char) => Literal::Char(char),
            Token::String(str) => Literal::String(str),
            Token::FString(str) => return Parser::parse_fstring(str).map(Literal::FString),
            Token::True => Literal::Bool(true),
            Token::False => Literal::Bool(false),
            Token::Hash => match stream.peek()? {
                Token::LBrace => stream.parse_map_literal(),
                Token::LBracket => stream.parse_tuple_literal(),
                got => {
                    Err(stream.expect_failed(got.kind(), &[TokenKind::LBrace, TokenKind::LParen]))
                }
            }?,
            got => {
                return Err(stream.expect_failed(got.kind(), &[
                    TokenKind::Int,
                    TokenKind::Char,
                    TokenKind::String,
                    TokenKind::Ident,
                ]));
            }
        })
    }
}

impl Parse for Pat {
    fn parse(stream: &mut Parser) -> Result<Self> {
        match stream.bump()? {
            Token::LBracket => {
                Ok(Self::Array(stream.parse_separated(TokenKind::Comma, TokenKind::RBracket)?))
            }
            Token::Ident(ident) => Ok(Self::Ident(ident)),
            got => Err(stream.expect_failed(got.kind(), &[TokenKind::Ident, TokenKind::LBracket])),
        }
    }
}

impl Parse for Expr {
    fn parse(stream: &mut Parser) -> Result<Self> {
        stream.parse_expr(0, true)
    }
}

impl Parse for ImplBlock {
    fn parse(stream: &mut Parser) -> Result<Self> {
        stream.expect_token(Token::Impl)?;
        let mut generics: Box<[Spanned<Ident>]> = Box::new([]);
        if stream.peek()? == Token::LBracket {
            stream.skip();
            generics = stream.parse_separated(TokenKind::Comma, TokenKind::RBracket)?;
        }
        let sig = stream.parse()?;
        let body = stream.parse()?;
        Ok(Self { generics, sig, body })
    }
}

impl Parse for ImplSig {
    fn parse(stream: &mut Parser) -> Result<Self> {
        Spanned::<ExplicitType>::parse(stream).map(Self::Inherent)
    }
}

impl Parse for Param {
    fn parse(stream: &mut Parser) -> Result<Self> {
        let ident = stream.parse()?;
        stream.expect_token(Token::Colon)?;
        let expl_ty = stream.parse()?;
        Ok(Self { ident, expl_ty })
    }
}

impl Parse for Path {
    fn parse(stream: &mut Parser) -> Result<Self> {
        let mut segments = vec![stream.parse()?];
        while stream.peek()? == Token::Colon {
            stream.skip();
            segments.push(stream.parse()?);
        }
        Ok(Self { segments: segments.into() })
    }
}
