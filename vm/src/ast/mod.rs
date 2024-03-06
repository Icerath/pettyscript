pub mod node;

pub use node::{BinOp, Expression, IfStatement, Keyword, Literal, Node, Statement, UnaryOp};

impl Statement {
    #[must_use]
    pub const fn node(self) -> Node {
        Node::Statement(self)
    }
}

impl From<Expression> for Node {
    fn from(expr: Expression) -> Self {
        Self::Expression(expr)
    }
}

impl From<Literal> for Node {
    fn from(literal: Literal) -> Self {
        Expression::Literal(literal).into()
    }
}

impl From<Statement> for Node {
    fn from(statement: Statement) -> Self {
        Self::Statement(statement)
    }
}

impl From<IfStatement> for Statement {
    fn from(value: IfStatement) -> Self {
        Self::IfStatement(value)
    }
}

impl From<IfStatement> for Node {
    fn from(value: IfStatement) -> Self {
        Statement::from(value).into()
    }
}

impl TryFrom<&str> for BinOp {
    type Error = ();

    fn try_from(input: &str) -> Result<Self, Self::Error> {
        let op = match input {
            "||" => Self::Or,
            "&&" => Self::And,
            "<" => Self::Lt,
            "<=" => Self::LtEq,
            ">" => Self::Gt,
            ">=" => Self::GtEq,
            "==" => Self::Eq,
            "!=" => Self::Ne,
            "|" => Self::BitOr,
            "^" => Self::Xor,
            "&" => Self::BitAnd,
            "<<" => Self::Shl,
            ">>" => Self::Shr,
            "+" => Self::Add,
            "-" => Self::Sub,
            "*" => Self::Mul,
            "/" => Self::Div,
            "%" => Self::Mod,
            "." => Self::Dot,
            "::" => Self::PathSep,
            ".." => Self::RangeExclusive,
            "..=" => Self::RangeInclusive,
            _ => return Err(()),
        };
        Ok(op)
    }
}

impl Node {
    pub fn block(nodes: impl Into<Box<[Self]>>) -> Self {
        Self::Statement(Statement::Block(nodes.into()))
    }
}
