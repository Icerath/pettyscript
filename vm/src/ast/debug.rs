use core::fmt;

use super::*;
use crate::prelude::PtyStr;

impl fmt::Debug for Expression {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(ident) => write!(f, "{ident}"),
            Self::UnaryExpr { op, expr } => write!(f, "{op:?}{expr:?}"),
            Self::BinExpr { op, args } => write!(f, "({:?} {op} {:?})", &args.0, &args.1),
            Self::FuncCall { name, args } => write!(f, "{name}({args:?})"),
            Self::Literal(literal) => write!(f, "{literal:?}"),
            Self::Keyword(keyword) => write!(f, "{keyword:?}"),
            Self::LineComment(comment) => writeln!(f, "//{comment}"),
        }
    }
}

impl fmt::Debug for Statement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Block(block) => write!(f, "{:?}", DebugBlock(block)),
            Self::ForLoop { ident, iter, block } => {
                write!(f, "for {ident} in {iter:?} {:?}", DebugBlock(block))
            }
            Self::WhileLoop { expr, block } => {
                write!(f, "while {expr:?} {:?}", DebugBlock(block))
            }
            Self::IfStatement(ifstatement) => write!(f, "{ifstatement:?}"),
            Self::VarDecl { name, expr } => write!(f, "let {name} = {expr:?}"),
            Self::VarAssign { name, expr } => write!(f, "{name} = {expr:?}"),
            Self::OpDecl { name, op, expr } => write!(f, "let {name} {op}= {expr:?}"),
            Self::OpAssign { name, op, expr } => write!(f, "{name} {op}= {expr:?}"),
            Self::FuncDecl { name, params, block } => {
                write!(f, "fn {name}({:?}) {:?}", DebugParams(params), DebugBlock(block))
            }
        }
    }
}

impl fmt::Debug for Literal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool(bool) => write!(f, "{bool}"),
            Self::Int(int) => write!(f, "{int}"),
            Self::Float(float) => write!(f, "{float}"),
            Self::String(str) => write!(f, "{str:?}"),
            Self::List(list) => write!(f, "{list:?}"),
            Self::Tuple(tuple) => write!(f, "Tuple({tuple:?})"),
            Self::Map(map) => {
                f.debug_map().entries(map.iter().map(|(lhs, rhs)| (lhs, rhs))).finish()
            }
            Self::Function { params, block } => write!(f, "fn({params:?}) {block:?}"),
        }
    }
}

impl fmt::Debug for Node {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Expression(expr) => write!(f, "{expr:?}"),
            Self::Statement(statement) => write!(f, "{statement:?}"),
        }
    }
}

struct DebugBlock<'a>(&'a [Node]);

impl fmt::Debug for DebugBlock<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_set().entries(self.0.iter()).finish()
    }
}
struct DebugParams<'a>(&'a [PtyStr]);

impl fmt::Debug for DebugParams<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for param in self.0 {
            write!(f, "{param}")?;
        }
        Ok(())
    }
}

impl fmt::Debug for IfStatement {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "if {:?} {:?}", self.condition, DebugBlock(&self.block))?;
        if let Some(node) = &self.or_else {
            write!(f, " else {node:?}")?;
        }
        Ok(())
    }
}

impl fmt::Display for BinOp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let symbol = match self {
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
        };
        write!(f, "{symbol}")
    }
}
