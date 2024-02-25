use core::fmt;
use std::rc::Rc;

use vm::{
    ast::{BinOp, Expression, IfStatement, Keyword, Literal, Node, Statement, UnaryOp},
    object::PtyStr,
};

#[non_exhaustive]
pub struct Config {
    pub indent_level: usize,
    pub replace_newline_with_space: bool,
}

impl Default for Config {
    fn default() -> Self {
        Self { indent_level: 4, replace_newline_with_space: false }
    }
}

#[must_use]
pub fn format_one(ast: &Node, config: Config) -> String {
    format_many(std::slice::from_ref(ast), config)
}

#[must_use]
pub fn format_many(ast: &[Node], config: Config) -> String {
    let mut f = Formatter::new(config);
    for node in ast {
        node.fmt(&mut f);
    }
    f.buf.truncate(f.buf.trim_end().len());
    f.buf.push('\n');
    // FIXME: breaks comments
    if f.config.replace_newline_with_space {
        f.buf = f.buf.replace('\n', " ");
    }
    f.buf
}

struct Formatter {
    buf: String,
    current_indent: usize,
    inside_bin_expr: bool,
    config: Rc<Config>,
}

impl Formatter {
    fn new(config: Config) -> Self {
        Self {
            buf: String::new(),
            current_indent: 0,
            inside_bin_expr: false,
            config: Rc::new(config),
        }
    }

    fn sub_fmt(&self) -> Self {
        Self {
            buf: String::new(),
            current_indent: self.current_indent,
            inside_bin_expr: self.inside_bin_expr,
            config: self.config.clone(),
        }
    }

    fn write<T: fmt::Display>(&mut self, val: T) {
        use fmt::Write;
        let _ = write!(&mut self.buf, "{val}");
    }

    /// The current line
    fn line(&self) -> &str {
        self.buf.lines().last().unwrap_or("")
    }
}

trait NodeFmt {
    fn fmt(&self, f: &mut Formatter);
}

struct Debug<T>(T);
impl<T: fmt::Debug> NodeFmt for Debug<T> {
    fn fmt(&self, f: &mut Formatter) {
        use std::fmt::Write;
        let _ = write!(&mut f.buf, "{:?}", self.0);
    }
}

struct Sep<'a, T>(&'a [T]);
impl<T: NodeFmt> NodeFmt for Sep<'_, T> {
    fn fmt(&self, f: &mut Formatter) {
        for (index, node) in self.0.iter().enumerate() {
            if index != 0 {
                ", ".fmt(f);
            }
            node.fmt(f);
        }
    }
}

struct Paren<T>(T);
impl<T: NodeFmt> NodeFmt for Paren<T> {
    fn fmt(&self, f: &mut Formatter) {
        ("(", &self.0, ")").fmt(f);
    }
}
struct Indent;
impl NodeFmt for Indent {
    fn fmt(&self, f: &mut Formatter) {
        for _ in 0..f.current_indent * f.config.indent_level {
            " ".fmt(f);
        }
    }
}
struct Align;
impl NodeFmt for Align {
    fn fmt(&self, f: &mut Formatter) {
        if f.buf.ends_with('}') {
            f.buf.push(' ');
        }
    }
}
struct Block<'a, T>(&'a [T]);

impl<T: NodeFmt> NodeFmt for Block<'_, T> {
    fn fmt(&self, f: &mut Formatter) {
        if self.0.len() == 1 {
            let mut sub_fmt = f.sub_fmt();
            (": ", &self.0[0]).fmt(&mut sub_fmt);
            if f.line().len() + sub_fmt.buf.len() < 80 {
                return f.buf.push_str(&sub_fmt.buf);
            }
        }
        if self.0.is_empty() {
            return " {}".fmt(f);
        }
        " {\n".fmt(f);
        f.current_indent += 1;
        for node in self.0 {
            (Indent, node, "\n").fmt(f);
        }
        f.current_indent -= 1;
        (Indent, "}").fmt(f);
    }
}

impl NodeFmt for Node {
    fn fmt(&self, f: &mut Formatter) {
        match self {
            Self::Expression(expr) => expr.fmt(f),
            Self::Statement(statement) => statement.fmt(f),
        }
    }
}

impl<T: NodeFmt> NodeFmt for &T {
    fn fmt(&self, f: &mut Formatter) {
        (*self).fmt(f);
    }
}

impl<T: NodeFmt> NodeFmt for Box<T> {
    fn fmt(&self, f: &mut Formatter) {
        self.as_ref().fmt(f);
    }
}

impl NodeFmt for Expression {
    fn fmt(&self, f: &mut Formatter) {
        match self {
            Self::BinExpr { op, args } => BinExpr { lhs: &args.0, op: *op, rhs: &args.1 }.fmt(f),
            Self::FuncCall { name, args } => {
                name.fmt(f);
                let temp = f.inside_bin_expr;
                f.inside_bin_expr = false;
                Paren(Sep(args)).fmt(f);
                f.inside_bin_expr = temp;
            }
            Self::Ident(ident) => ident.fmt(f),
            Self::Keyword(keyword) => keyword.fmt(f),
            Self::LineComment(comment) => ("//", comment).fmt(f),
            Self::Literal(literal) => literal.fmt(f),
            Self::UnaryExpr { op, expr } => (op, expr).fmt(f),
        }
    }
}

struct BinExpr<'a> {
    lhs: &'a Expression,
    op: BinOp,
    rhs: &'a Expression,
}

impl NodeFmt for BinExpr<'_> {
    fn fmt(&self, f: &mut Formatter) {
        let Self { lhs, op, rhs } = self;
        if f.inside_bin_expr && !matches!(lhs, Expression::BinExpr { .. }) {
            match op {
                BinOp::RangeInclusive | BinOp::RangeExclusive | BinOp::Dot => {
                    Paren((lhs, op, rhs)).fmt(f);
                }
                _ => Paren((lhs, " ", op, " ", rhs)).fmt(f),
            }
        } else {
            f.inside_bin_expr = true;
            match op {
                BinOp::RangeInclusive | BinOp::RangeExclusive | BinOp::Dot => (lhs, op, rhs).fmt(f),
                _ => (lhs, " ", op, " ", rhs).fmt(f),
            }
            f.inside_bin_expr = false;
        }
    }
}

impl NodeFmt for BinOp {
    fn fmt(&self, f: &mut Formatter) {
        self.symbol().fmt(f);
    }
}

impl NodeFmt for Statement {
    fn fmt(&self, f: &mut Formatter) {
        match self {
            Self::Block(block) => Block(block).fmt(f),
            Self::ForLoop { ident, iter, block } => {
                ("for ", ident, " in ", iter, Block(block)).fmt(f);
            }
            Self::FuncDecl { name, params, block } => {
                ("fn ", name, Paren(Sep(params)), Block(block), "\n\n").fmt(f);
            }
            Self::IfStatement(if_statement) => if_statement.fmt(f),
            Self::OpAssign { name, op, expr } => (name, " ", op, "= ", expr).fmt(f),
            Self::OpDecl { name, op, expr } => ("let ", name, " ", op, "= ", expr).fmt(f),
            Self::VarAssign { name, expr } => (name, " = ", expr).fmt(f),
            Self::VarDecl { name, expr } => ("let ", name, " = ", expr).fmt(f),
            Self::WhileLoop { expr, block } => ("while ", expr, Block(block)).fmt(f),
        }
    }
}

impl NodeFmt for Keyword {
    fn fmt(&self, f: &mut Formatter) {
        match self {
            Self::Break => "break".fmt(f),
            Self::Return(expr) => {
                ("return", expr.as_ref().map(|expr| (" ", expr))).fmt(f);
            }
        }
    }
}

impl NodeFmt for Literal {
    fn fmt(&self, f: &mut Formatter) {
        match self {
            Self::Bool(bool) => f.write(bool),
            Self::Closure { params, block } => ("|", Sep(params), "|", Block(block)).fmt(f),
            Self::Float(float) => f.write(float),
            Self::Int(int) => f.write(int),
            Self::List(list) => ("[", Sep(list), "]").fmt(f),
            Self::Map(map) => todo!("{map:?}"),
            Self::String(str) => Debug(str).fmt(f),
            Self::Tuple(tuple) => Paren(Sep(tuple)).fmt(f),
        }
    }
}

impl NodeFmt for UnaryOp {
    fn fmt(&self, f: &mut Formatter) {
        match self {
            Self::Neg => "-".fmt(f),
            Self::Not => "!".fmt(f),
        }
    }
}

impl NodeFmt for IfStatement {
    fn fmt(&self, f: &mut Formatter) {
        ("if ", &self.condition, Block(&self.block)).fmt(f);
        let Some(or_else) = &self.or_else else { return };
        if self.block.len() <= 1 {
            ("\n", Indent).fmt(f);
        }
        match or_else.as_ref() {
            Node::Statement(Statement::Block(block)) => (Align, "else", Block(block)).fmt(f),
            or_else => (Align, "else ", or_else).fmt(f),
        }
    }
}

impl<T: NodeFmt> NodeFmt for Option<T> {
    fn fmt(&self, f: &mut Formatter) {
        if let Some(inner) = self {
            inner.fmt(f);
        }
    }
}

impl NodeFmt for char {
    fn fmt(&self, f: &mut Formatter) {
        f.buf.push(*self);
    }
}

impl NodeFmt for &str {
    fn fmt(&self, f: &mut Formatter) {
        f.buf.push_str(self);
    }
}

impl NodeFmt for PtyStr {
    fn fmt(&self, f: &mut Formatter) {
        f.buf.push_str(self);
    }
}

impl NodeFmt for String {
    fn fmt(&self, f: &mut Formatter) {
        f.buf.push_str(self);
    }
}

macro_rules! impl_tuple {
    ($($ty:tt),*) => {
        impl<$($ty: NodeFmt,)*> NodeFmt for ($($ty),*,) {
            #[allow(non_snake_case)]
            fn fmt(&self, f: &mut Formatter) {
                match self {
                    ($($ty),+) => ($($ty.fmt(f)),+)
                };
            }
        }
    };
}

impl_tuple!(A, B);
impl_tuple!(A, B, C);
impl_tuple!(A, B, C, D);
impl_tuple!(A, B, C, D, E);
impl_tuple!(A, B, C, D, E, F);
impl_tuple!(A, B, C, D, E, F, G);
