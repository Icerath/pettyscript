use std::fmt;

use logos::Logos;

use crate::intern::intern;

#[derive(Debug, Logos, Clone, PartialEq, macros::EnumKind)]
#[enum_kind(TokenKind)]
#[logos(skip "//[^\n]*")]
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
    #[token("#")] Hash,
    // Keywords
    #[token("or")] #[token("||")] Or,
    #[token("and")] #[token("&&")] And,
    #[token("if")] If,
    #[token("else")] Else,
    #[token("in")] In,
    #[token("impl")] Impl,
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
    #[token("'", lex_character)]
    Char(char),
    #[regex(r"\d[\d_]*", parse_int)]
    #[regex(r"0[bB][01_]+", parse_binary_int)]
    #[regex(r"0[xX][\da-fA-F_]+", parse_hex_int)]
    #[regex(r"0[oO][0-7_]+", parse_octal_int)]
    Int(i64),
    #[regex(r#"""#, lex_string)]
    String(S),
    #[token(r#"f""#, lex_fstring)]
    FString(S),
    #[regex(r"[a-zA-Z_][a-zA-Z_\d]*", |lex| intern(lex.slice()))]
    Ident(S),
}

fn lex_character(lexer: &mut Lexer) -> Option<char> {
    let mut rem = lexer.remainder().chars();
    let char = match rem.next()? {
        '\\' => match rem.next()? {
            'n' => '\n',
            '\'' => '\'',
            _ => return None,
        },
        other => other,
    };
    if rem.next()? != '\'' {
        return None;
    }
    lexer.bump(lexer.remainder().len() - rem.as_str().len());
    Some(char)
}

fn lex_string(lexer: &mut Lexer) -> Option<S> {
    // TODO: More string escaping
    let mut rem = lexer.remainder().chars();
    let mut out = String::new();
    loop {
        match rem.next()? {
            '\\' if rem.clone().next()? == 'n' => {
                let _ = rem.next();
                out.push('\n');
            }
            '\\' if rem.clone().next()? == '"' => {
                let _ = rem.next();
                out.push('"');
            }
            '"' => break,
            next => out.push(next),
        }
    }
    lexer.bump(lexer.remainder().len() - rem.as_str().len());
    Some(intern(&out))
}

fn lex_fstring(lexer: &mut Lexer) -> Option<S> {
    // TODO: String escaping
    // TODO: Handle Braces inside substrings.
    let mut rem = lexer.remainder().chars();
    loop {
        let next = rem.next()?;
        match next {
            '{' => {}
            '"' => break,
            _ => continue,
        }
        let mut lbraces = 1;
        while lbraces != 0 {
            match rem.next()? {
                '{' => lbraces += 1,
                '}' => lbraces -= 1,
                _ => {}
            }
        }
    }
    let chars_eaten = lexer.remainder().len() - rem.as_str().len();
    let string = intern(&lexer.remainder()[..chars_eaten - 1]);
    lexer.bump(chars_eaten);
    Some(string)
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

// avoid Logos' special case for &str
type S = &'static str;

impl Token {
    pub fn kind(&self) -> TokenKind {
        TokenKind::from(self)
    }
}

impl TokenKind {
    pub fn repr(self) -> &'static str {
        match self {
            Self::Hash => "#",
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
            Self::Impl => "impl",
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
            Self::FString => "fstring",
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
