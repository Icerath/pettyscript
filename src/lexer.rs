use std::fmt;

use enum_kinds::EnumKind;
use logos::Logos;

use crate::intern::intern;

#[derive(Default, Debug, Clone, PartialEq, thiserror::Error)]
pub enum Error {
    #[error(transparent)]
    FromIntErr(#[from] std::num::ParseIntError),
    #[default]
    #[error("Unknown")]
    Unknown,
}

#[derive(Debug, Logos, Clone, Copy, PartialEq, EnumKind)]
#[enum_kind(TokenKind)]
#[logos(error = Error)]
#[logos(skip "//[^\n]*\n")]
#[logos(skip "[ \t\r\n]")]
#[rustfmt::skip]
pub enum Token {
    // Symbols
    #[token("(")] LParen,
    #[token(")")] RParen,
    #[token("{")] LBrace,
    #[token("[")] LBracket,
    #[token("]")] RBracket,
    #[token("}")] RBrace,
    #[token(",")] Comma,
    #[token(".")] Dot,
    #[token("!")] Bang,
    #[token(":")] Colon,
    #[token(";")] Semicolon,
    #[token("+")] Plus,
    #[token("-")] Minus,
    #[token("*")] Star,
    #[token("/")] Slash,
    #[token("%")] Percent,
    #[token("|")] Pipe,
    #[token("&")] Ampersand,
    #[token(">")] RAngle,
    #[token("<")] LAngle,
    #[token(">=")] RAngleEq,
    #[token("<=")] LAngleEq,
    #[token("=")] Eq,
    #[token("==")] EqEq,
    #[token("!=")] BangEq,
    #[token("..")] Range,
    #[token("..=")] RangeInclusive,
    // Keywords
    #[token("or")] #[token("||")] Or,
    #[token("and")] #[token("&&")] And,
    #[token("if")] If,
    #[token("else")] Else,
    #[token("in")] In,
    #[token("fn")] Fn,
    #[token("for")] For,
    #[token("while")] While,
    #[token("let")] Let,
    #[token("const")] Const,
    #[token("continue")] Continue,
    #[token("break")] Break,
    #[token("return")] Return,
    #[token("struct")] Struct,
    #[token("enum")] Enum,
    #[token("true")] True,
    #[token("false")] False,
    // Literals
    #[regex("'[^']'", |lex| lex.slice().chars().next().unwrap())]
    Char(char),
    #[regex(r"\d[\d_]*", |lex| lex.slice().parse())]
    Int(i128),
    #[regex(r#""[^"]*""#, |lex| intern(&lex.slice()[1..lex.slice().len() - 1]))]
    String(S),
    #[regex(r"[a-zA-Z_][a-zA-Z_\d]*", |lex| intern(lex.slice()))]
    Ident(S),
}

// avoid Logos' special case for &str
type S = &'static str;

impl Token {
    pub fn kind(self) -> TokenKind {
        TokenKind::from(self)
    }
}

impl TokenKind {
    pub fn repr(self) -> &'static str {
        match self {
            Self::True => "true",
            Self::False => "false",
            Self::Or => "or",
            Self::And => "and",
            Self::Ampersand => "&",
            Self::Bang => "!",
            Self::BangEq => "!=",
            Self::Comma => ",",
            Self::Dot => ".",
            Self::Eq => "=",
            Self::EqEq => "==",
            Self::Fn => "fn",
            Self::For => "for",
            Self::While => "while",
            Self::If => "if",
            Self::Continue => "continue",
            Self::Break => "break",
            Self::Else => "else",
            Self::Ident => "identifier",
            Self::In => "in",
            Self::Int => "int",
            Self::LAngle => "<",
            Self::LAngleEq => "<=",
            Self::LBrace => "{",
            Self::LBracket => "[",
            Self::LParen => "(",
            Self::Minus => "-",
            Self::Percent => "%",
            Self::Pipe => "|",
            Self::Plus => "+",
            Self::RAngle => ">",
            Self::RAngleEq => ">=",
            Self::RBrace => "}",
            Self::RBracket => "]",
            Self::RParen => ")",
            Self::Range => "..",
            Self::RangeInclusive => "..=",
            Self::Return => "return",
            Self::Semicolon => ";",
            Self::Colon => ":",
            Self::Slash => "/",
            Self::Star => "*",
            Self::Char => "char",
            Self::String => "string",
            Self::Struct => "struct",
            Self::Enum => "enum",
            Self::Let => "let",
            Self::Const => "const",
        }
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.kind())
    }
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.repr())
    }
}
