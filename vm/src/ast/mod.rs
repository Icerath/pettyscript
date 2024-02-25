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

impl Node {
    pub fn block(nodes: impl Into<Box<[Self]>>) -> Self {
        Self::Statement(Statement::Block(nodes.into()))
    }
}
