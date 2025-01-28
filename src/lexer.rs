use std::fmt;

use logos::Logos;

use crate::intern::intern;

#[derive(Debug, Logos, Clone, Copy, PartialEq, macros::EnumKind)]
#[enum_kind(TokenKind)]
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
    #[token("->")] ThinArrow,
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
    #[regex("'[^']'", |lex| lex.slice()[1..].chars().next().unwrap())]
    Char(char),
    #[regex(r"\d[\d_]*", parse_int)]
    #[regex(r"0[bB][01_]+", parse_binary_int)]
    #[regex(r"0[xX][\da-fA-F_]+", parse_hex_int)]
    #[regex(r"0[oO][0-7_]+", parse_octal_int)]
    Int(i64),
    #[regex(r#""[^"]*""#, string_escape)]
    String(S),
    #[regex(r"[a-zA-Z_][a-zA-Z_\d]*", |lex| intern(lex.slice()))]
    Ident(S),
}

type Lexer<'a> = logos::Lexer<'a, Token>;

fn parse_hex_int(str: &mut Lexer) -> Option<i64> {
    let mut sum = 0;
    for c in str.slice()[2..].bytes() {
        match c {
            b'0'..=b'9' => sum = sum * 16 + (c - b'0') as i64,
            b'a'..=b'f' => sum = sum * 16 + (c - b'a' + 10) as i64,
            b'A'..=b'F' => sum = sum * 16 + (c - b'A' + 10) as i64,
            b'_' => {}
            _ => return None,
        }
    }
    Some(sum)
}

fn parse_octal_int(str: &mut Lexer) -> Option<i64> {
    let mut sum = 0;
    for c in str.slice()[2..].bytes() {
        match c {
            b'0'..=b'7' => sum = sum * 8 + (c - b'0') as i64,
            _ => return None,
        }
    }
    Some(sum)
}

fn parse_binary_int(str: &mut Lexer) -> Option<i64> {
    let mut sum = 0;
    for c in str.slice()[2..].bytes() {
        match c {
            b'0' => sum *= 2,
            b'1' => sum = sum * 2 + 1,
            b'_' => {}
            _ => return None,
        }
    }
    Some(sum)
}

fn parse_int(str: &mut Lexer) -> Option<i64> {
    let mut sum = 0;
    for c in str.slice().bytes() {
        match c {
            b'0'..=b'9' => sum = sum * 10 + (c - b'0') as i64,
            b'_' => {}
            _ => return None,
        }
    }
    Some(sum)
}

fn string_escape(lex: &mut Lexer) -> &'static str {
    // TODO: Impl proper string escaping
    intern(&lex.slice()[1..lex.slice().len() - 1].replace(r"\n", "\n"))
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
            Self::ThinArrow => "->",
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
