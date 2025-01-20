use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    bytecode::{BytecodeBuilder, Constant, Op},
    parser::*,
};

pub fn codegen(ast: &[Stmt]) -> Vec<u8> {
    let mut codegen = Codegen::new();
    codegen.load_builtins();
    codegen.gen_block(ast);
    codegen.finish()
}

enum Type {
    Struct { fields: FxHashSet<&'static str> },
    Enum { variants: FxHashSet<&'static str> },
    Function { nparams: usize },
}

#[derive(Default)]
struct Scope {
    types: FxHashMap<&'static str, Type>,
}

struct Codegen {
    builder: BytecodeBuilder,
    scopes: Vec<Scope>,
}

impl Codegen {
    fn new() -> Self {
        Self { builder: BytecodeBuilder::default(), scopes: vec![] }
    }

    fn load_builtins(&mut self) {
        self.builder.insert_identifer("println");
    }

    fn gen_block(&mut self, ast: &[Stmt]) {
        for node in ast {
            self.scopes.push(Scope::default());
            self.r#gen(node);
        }
    }

    fn gen(&mut self, node: &Stmt) {
        match node {
            Stmt::Struct(Struct { ident, fields }) => {
                self.scope()
                    .types
                    .insert(ident, Type::Struct { fields: fields.iter().copied().collect() });
            }
            Stmt::Enum(Enum { ident, variants }) => {
                self.scope()
                    .types
                    .insert(ident, Type::Enum { variants: variants.iter().copied().collect() });
            }
            Stmt::Function(Function { ident, params, body }) => {
                self.scope().types.insert(ident, Type::Function { nparams: params.len() });
                self.gen_block(&body.stmts);
            }
            Stmt::Assign(_) => todo!(),
            Stmt::ForLoop(ForLoop { ident, iter, body }) => {
                self.scopes.push(Scope::default());
                self.expr(iter);
                let start_label = self.builder.create_label();
                self.builder.insert_label(start_label);
                self.builder.insert(Op::IterNext);
                let end_label = self.builder.create_label();
                self.builder.insert(Op::CJump(end_label));
                let ident = self.builder.insert_identifer(ident);
                self.builder.insert(Op::Store(ident));
                self.gen_block(&body.stmts);
                self.builder.insert(Op::Jump(start_label));
                self.builder.insert_label(end_label);
            }
            Stmt::IfChain(IfChain { first, else_ifs, r#else }) => {
                self.expr(&first.condition);
                let final_end_label = self.builder.create_label();
                let mut next_label = self.builder.create_label();
                self.builder.insert(Op::CJump(next_label));
                self.gen_block(&first.body.stmts);
                self.builder.insert(Op::Jump(final_end_label));
                for elseif in else_ifs {
                    self.builder.insert_label(next_label);
                    self.expr(&elseif.condition);
                    next_label = self.builder.create_label();
                    self.builder.insert(Op::CJump(next_label));
                    self.gen_block(&elseif.body.stmts);
                    self.builder.insert(Op::Jump(final_end_label));
                }
                self.builder.insert_label(next_label);
                if let Some(block) = r#else {
                    self.gen_block(&block.stmts);
                }
                self.builder.insert_label(final_end_label);
            }
            Stmt::Expr(expr) => {
                self.expr(expr);
                self.builder.insert(Op::Pop);
            }
            _ => todo!("{node:?}"),
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Literal(literal) => match literal {
                Literal::Int(int) => {
                    let constant = self.builder.insert_constant(Constant::Int(*int as _));
                    self.builder.insert(Op::LoadConst(constant));
                }
                Literal::Ident(ident) => {
                    let key = self.builder.insert_identifer(ident);
                    self.builder.insert(Op::Load(key));
                }
                Literal::String(string) => {
                    let key = self.builder.insert_constant(Constant::String(string));
                    self.builder.insert(Op::LoadConst(key));
                }
                _ => todo!("{literal:?}"),
            },
            Expr::Binary { op, exprs } => {
                let op = match op {
                    BinOp::Range => Op::Range,
                    BinOp::RangeInclusive => Op::RangeInclusive,
                    BinOp::Eq => Op::Eq,
                    BinOp::Mod => Op::Mod,
                    _ => todo!("{op:?}"),
                };
                self.expr(&exprs[0]);
                self.expr(&exprs[1]);
                self.builder.insert(op);
            }
            Expr::FnCall { function, args } => {
                for arg in args {
                    self.expr(arg);
                }
                self.expr(function);
                self.builder.insert(Op::FnCall { numargs: args.len() as u8 });
            }
            _ => todo!("{expr:?}"),
        }
    }

    fn scope(&mut self) -> &mut Scope {
        self.scopes.last_mut().unwrap()
    }

    fn finish(self) -> Vec<u8> {
        self.builder.finish()
    }
}
