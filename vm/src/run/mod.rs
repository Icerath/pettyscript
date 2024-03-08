use std::collections::HashMap;

use crate::ast::node::{Block, OrElse};
use crate::ast::{BinOp, Expression, IfStatement, Keyword, Literal, Node, Statement, UnaryOp};
use crate::object::List;
use crate::{prelude::*, stdlib};

#[derive(Debug)]
pub enum ControlFlow {
    Break,
    Return(PettyObject),
    Continue,
}

pub struct Vm {
    pub variables: RefCell<HashMap<PtyStr, PettyObject>>,
    pub control_flow: RefCell<Option<ControlFlow>>,
}

impl Vm {
    #[allow(clippy::new_without_default, clippy::must_use_candidate)]
    pub fn new() -> Self {
        let vm = Self { variables: RefCell::default(), control_flow: RefCell::new(None) };
        stdlib::init(&vm);
        vm
    }

    pub fn run_main(&self) {
        let Some(main) = self.variables.borrow().get("main").cloned() else {
            return;
        };
        main.call(self, FnArgs::new(&[]));
    }

    pub fn exec_many(&self, nodes: &[Node]) {
        for node in nodes {
            if self.control_flow.borrow().is_some() {
                return;
            }
            self.exec(node);
        }
    }

    pub fn exec_block(&self, block: &Block) {
        match block {
            Block::Single(expr) => _ = self.eval(expr),
            Block::Multi(nodes) => self.exec_many(nodes),
        }
    }

    /// # Panics
    pub fn exec(&self, node: &Node) {
        match node {
            Node::Expression(Expression::LineComment(_)) => {}
            Node::Expression(expr) => _ = self.eval(expr),
            Node::Statement(statement) => match statement {
                Statement::Block(nodes) => self.exec_many(nodes),
                Statement::ClassDecl { name: _, params: _ } => todo!(),
                Statement::ForLoop { ident, iter, block } => {
                    let into_iter = self.eval(iter);
                    let iter = into_iter.get(self, "__iter__");

                    loop {
                        let next = iter.get(self, "__next__");
                        // TODO: Proper iteration
                        if next.is_null() {
                            break;
                        }
                        self.variables.borrow_mut().insert(ident.clone(), next);
                        self.exec_block(block);
                        match &mut *self.control_flow.borrow_mut() {
                            control_flow @ Some(ControlFlow::Break) => break *control_flow = None,
                            Some(ControlFlow::Return(_)) => break,
                            control_flow @ Some(ControlFlow::Continue) => *control_flow = None,
                            _ => {}
                        }
                    }
                }
                Statement::FuncDecl { path, params, ret_type: _, block } => {
                    assert_eq!(path.segments.len(), 1);
                    let name = path.segments[0].clone();

                    let params = params.iter().map(|param| param.ident.clone()).collect();
                    let func = Rc::new(Func { params, body: block.clone() });
                    self.variables.borrow_mut().insert(name, func.into());
                }
                Statement::IfStatement(r#if) => self.exec_if(r#if),
                Statement::VarDecl { param, expr } => {
                    let value = self.eval(expr);
                    self.variables.borrow_mut().insert(param.ident.clone(), value);
                }
                Statement::VarAssign { name, expr } => {
                    let value = self.eval(expr);
                    *self
                        .variables
                        .borrow_mut()
                        .get_mut(name)
                        .expect("Value should already be declared for assignment") = value;
                }
                Statement::OpAssign { name, op, expr } => {
                    // TODO: Inplace operator assignment
                    let rhs = self.eval(expr);
                    let var = self.variables.borrow().get(name).unwrap().clone();
                    let new = var.get(self, op.method()).call(self, FnArgs::new(&[var, rhs]));
                    self.variables.borrow_mut().insert(name.clone(), new);
                }
                Statement::WhileLoop { expr, block } => loop {
                    let condition = self.eval(expr);
                    let condition =
                        condition.get(self, "__bool__").call(self, FnArgs::new(&[condition]));
                    match condition {
                        PettyObject::Bool(true) => self.exec_block(block),
                        PettyObject::Bool(false) => break,
                        _ => unreachable!("__bool__ should always return a bool"),
                    }
                    match &mut *self.control_flow.borrow_mut() {
                        control_flow @ Some(ControlFlow::Break) => break *control_flow = None,
                        Some(ControlFlow::Return(_)) => break,
                        control_flow @ Some(ControlFlow::Continue) => *control_flow = None,
                        _ => {}
                    }
                },
            },
        }
    }

    pub fn exec_if(&self, node: &IfStatement) {
        let IfStatement { condition, block, or_else } = node;
        let condition = self.eval(condition);
        let condition = condition.get(self, "__bool__").call(self, FnArgs::new(&[condition]));
        match condition {
            PettyObject::Bool(true) => {
                self.exec_block(block);
            }
            PettyObject::Bool(false) => match or_else {
                Some(OrElse::Block(block)) => self.exec_block(block),
                Some(OrElse::If(r#if)) => self.exec_if(r#if),
                None => {}
            },
            _ => unimplemented!(),
        }
    }

    /// # Panics
    pub fn eval(&self, expr: &Expression) -> PettyObject {
        match expr {
            Expression::Literal(literal) => match literal {
                Literal::Bool(bool) => (*bool).into(),
                Literal::Int(int) => PettyObject::Int(*int),
                Literal::Float(float) => PettyObject::Float(*float),
                Literal::String(str) => PettyObject::PtyStr(str.clone()),
                Literal::List(list) => {
                    PettyObject::List(List::new(list.iter().map(|expr| self.eval(expr)).collect()))
                }
                Literal::Map(_) => todo!(),
                Literal::Tuple(_) => todo!(),
                Literal::Closure { params: _, block: _ } => todo!(),
            },
            Expression::Ident(ident) => self
                .variables
                .borrow()
                .get(ident)
                .unwrap_or_else(|| {
                    panic!("Tried to get '{ident}' from {:#?}", self.variables.borrow().keys())
                })
                .clone(),
            Expression::Keyword(Keyword::Break) => {
                *self.control_flow.borrow_mut() = Some(ControlFlow::Break);
                PettyObject::NULL
            }
            Expression::Keyword(Keyword::Return(ret)) => {
                let ret = ret.as_ref().map_or(NULL, |ret| self.eval(ret));
                *self.control_flow.borrow_mut() = Some(ControlFlow::Return(ret));
                PettyObject::NULL
            }
            Expression::Keyword(Keyword::Continue) => {
                *self.control_flow.borrow_mut() = Some(ControlFlow::Continue);
                PettyObject::NULL
            }
            Expression::UnaryExpr { op, expr } => {
                self.eval(expr).get(self, op.method()).call(self, FnArgs::new(&[]))
            }
            Expression::FuncCall { expr, args } => {
                let expr = self.eval(expr);
                let args = args.iter().map(|arg| self.eval(arg)).collect::<Vec<_>>();
                expr.call(self, FnArgs::new(&args))
            }
            Expression::BinExpr { op, args } => {
                // TODO: Short circuting for conditionals
                let lhs = self.eval(&args.0);
                let rhs = self.eval(&args.1);

                match op {
                    BinOp::RangeInclusive | BinOp::RangeExclusive => match (op, lhs, rhs) {
                        (BinOp::RangeExclusive, PettyObject::Int(lhs), PettyObject::Int(rhs)) => {
                            (lhs..rhs).into()
                        }
                        (BinOp::RangeInclusive, PettyObject::Int(lhs), PettyObject::Int(rhs)) => {
                            (lhs..=rhs).into()
                        }
                        _ => panic!("Incorrect args {args:?}"),
                    },
                    BinOp::Lt | BinOp::LtEq | BinOp::Gt | BinOp::GtEq => {
                        match lhs.call_method(self, "__cmp__", &[rhs]) {
                            PettyObject::Int(0) => [BinOp::GtEq, BinOp::LtEq].contains(op),
                            PettyObject::Int(1) => [BinOp::Gt, BinOp::GtEq].contains(op),
                            PettyObject::Int(-1) => [BinOp::Lt, BinOp::LtEq].contains(op),
                            _ => unimplemented!(),
                        }
                        .into()
                    }
                    _ => {
                        let lhs = self.eval(&args.0);
                        let rhs = self.eval(&args.1);
                        let function = lhs.get(self, op.method());
                        function.call(self, FnArgs::new(&[lhs, rhs]))
                    }
                }
            }
            Expression::LineComment(_) => unreachable!(),
        }
    }
}

impl UnaryOp {
    const fn method(self) -> &'static str {
        match self {
            Self::Not => "__not__",
            Self::Neg => "__neg__",
        }
    }
}

impl BinOp {
    fn method(self) -> &'static str {
        match self {
            Self::Add => "__add__",
            Self::Sub => "__sub__",
            Self::Mul => "__mul__",
            Self::RangeInclusive | Self::RangeExclusive => {
                unreachable!("This should never be called for ranges")
            }
            Self::Mod => "__mod__",
            Self::Eq => "__eq__",
            op => todo!("{op:?}"),
        }
    }
}
