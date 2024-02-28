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
        (node, NewLine).fmt(&mut f);
    }
    f.buf.truncate(f.buf.trim_end().len());
    f.buf.push('\n');
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

    fn write<T: std::fmt::Display>(&mut self, val: T) {
        use std::fmt::Write;
        let _ = write!(&mut self.buf, "{val}");
    }

    /// The current line
    fn line(&self) -> &str {
        self.buf.lines().last().unwrap_or("")
    }
}

trait NodeFmt: Sized {
    fn fmt(&self, f: &mut Formatter);
    fn paren(self) -> impl NodeFmt {
        Fmt(move |f: &mut Formatter| ('(', &self, ')').fmt(f))
    }
}

trait NodeExt {
    fn block(self) -> impl NodeFmt;
    fn sep(self) -> impl NodeFmt;
}

impl<'a, T: NodeFmt> NodeExt for &'a [T] {
    fn sep(self) -> impl NodeFmt {
        Fmt(move |f: &mut Formatter| {
            for (index, node) in self.iter().enumerate() {
                if index != 0 {
                    ", ".fmt(f);
                }
                node.fmt(f);
            }
        })
    }

    fn block(self) -> impl NodeFmt {
        Fmt(move |f: &mut Formatter| {
            if self.is_empty() {
                return " {}".fmt(f);
            }
            if self.len() == 1 {
                let mut sub_fmt = f.sub_fmt();
                self[0].fmt(&mut sub_fmt);
                if f.line().len() + sub_fmt.buf.len() < 80 {
                    return (": ", &sub_fmt.buf).fmt(f);
                }
            }
            (" {", RawNewLine).fmt(f);
            f.current_indent += 1;
            for node in self {
                (Indent, node, RawNewLine).fmt(f);
            }
            f.current_indent -= 1;
            (Indent, "}").fmt(f);
        })
    }
}

struct Debug<T>(T);
impl<T: std::fmt::Debug> NodeFmt for Debug<T> {
    fn fmt(&self, f: &mut Formatter) {
        use std::fmt::Write;
        let _ = write!(&mut f.buf, "{:?}", self.0);
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
struct RawNewLine;
impl NodeFmt for RawNewLine {
    fn fmt(&self, f: &mut Formatter) {
        if f.config.replace_newline_with_space {
            " ".fmt(f);
        } else {
            "\n".fmt(f);
        }
    }
}

struct NewLine;
impl NodeFmt for NewLine {
    fn fmt(&self, f: &mut Formatter) {
        (RawNewLine, Indent).fmt(f);
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
            Self::FuncCall { expr, args } => FuncCall { expr, args }.fmt(f),
            Self::Ident(ident) => ident.fmt(f),
            Self::Keyword(keyword) => keyword.fmt(f),
            Self::LineComment(comment) => ("//", comment).fmt(f),
            Self::Literal(literal) => literal.fmt(f),
            Self::UnaryExpr { op, expr } => (op, expr).fmt(f),
        }
    }
}

struct FuncCall<'a> {
    expr: &'a Expression,
    args: &'a [Expression],
}

impl NodeFmt for FuncCall<'_> {
    fn fmt(&self, f: &mut Formatter) {
        match self.expr {
            Expression::BinExpr { .. }
            | Expression::UnaryExpr { .. }
            | Expression::Literal(Literal::Closure { .. }) => self.expr.paren().fmt(f),
            _ => self.expr.fmt(f),
        };
        let temp = f.inside_bin_expr;
        f.inside_bin_expr = false;
        self.args.sep().paren().fmt(f);
        f.inside_bin_expr = temp;
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
                    (lhs, op, rhs).paren().fmt(f);
                }
                _ => (lhs, " ", op, " ", rhs).paren().fmt(f),
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
            Self::Block(block) => block.block().fmt(f),
            Self::ForLoop { ident, iter, block } => {
                ("for ", ident, " in ", iter, block.block()).fmt(f);
            }
            Self::FuncDecl { name, params, block } => {
                ("fn ", name, params.sep().paren(), block.block(), NewLine).fmt(f);
            }
            Self::IfStatement(if_statement) => if_statement.fmt(f),
            Self::OpAssign { name, op, expr } => (name, " ", op, "= ", expr).fmt(f),
            Self::VarAssign { name, expr } => (name, " = ", expr).fmt(f),
            Self::VarDecl { name, expr } => ("let ", name, " = ", expr).fmt(f),
            Self::WhileLoop { expr, block } => ("while ", expr, block.block()).fmt(f),
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
            Self::Closure { params, block } => ("|", params.sep(), "|", block.block()).fmt(f),
            Self::Float(float) => f.write(float),
            Self::Int(int) => f.write(int),
            Self::List(list) => ("[", list.sep(), "]").fmt(f),
            Self::Map(map) => todo!("{map:?}"),
            Self::String(str) => Debug(str).fmt(f),
            Self::Tuple(tuple) => tuple.sep().paren().fmt(f),
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
        ("if ", &self.condition, self.block.block()).fmt(f);
        let Some(or_else) = &self.or_else else { return };
        if self.block.len() <= 1 {
            NewLine.fmt(f);
        }
        match or_else.as_ref() {
            Node::Statement(Statement::Block(block)) => (Align, "else", block.block()).fmt(f),
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

struct Fmt<F>(F);
impl<F: Fn(&mut Formatter)> NodeFmt for Fmt<F> {
    fn fmt(&self, f: &mut Formatter) {
        (self.0)(f);
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
