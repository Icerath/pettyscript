use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    bytecode::{BytecodeBuilder, Op},
    parser::*,
};

pub fn codegen(ast: &[Stmt]) -> Vec<u8> {
    let mut codegen = Codegen::default();
    codegen.gen_block(ast);
    let main = codegen.builder.insert_identifer("main");
    codegen.builder.insert(Op::Load(main));
    codegen.builder.insert(Op::FnCall { numargs: 0 });
    codegen.finish()
}

#[expect(unused)]
enum Type {
    Struct { fields: FxHashSet<&'static str> },
    Enum { variants: FxHashSet<&'static str> },
    Function { nparams: usize },
}

#[derive(Default)]
struct Scope {
    types: FxHashMap<&'static str, Type>,
}

#[derive(Default)]
struct Codegen {
    builder: BytecodeBuilder,
    scopes: Vec<Scope>,
    continue_label: Option<u32>,
    break_label: Option<u32>,
}

impl Codegen {
    fn gen_block(&mut self, ast: &[Stmt]) {
        for node in ast {
            self.scopes.push(Scope::default());
            self.r#gen(node);
            self.scopes.pop();
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

                let ident_key = self.builder.insert_identifer(ident);

                let function_start = self.builder.create_label();
                let function_end = self.builder.create_label();

                self.builder.insert(Op::CreateFunction { label: function_start });
                self.builder.insert(Op::Store(ident_key));

                self.builder.insert(Op::Jump(function_end));
                self.builder.insert_label(function_start);

                self.gen_block(&body.stmts);

                self.builder.insert(Op::LoadNull);
                self.builder.insert(Op::Ret);

                self.builder.insert_label(function_end);
            }
            Stmt::Let(VarDecl { ident, expr }) | Stmt::Const(VarDecl { ident, expr }) => {
                match expr {
                    Some(expr) => self.expr(expr),
                    None => self.builder.insert(Op::LoadNull),
                }
                let ident = self.builder.insert_identifer(ident);
                self.builder.insert(Op::Store(ident));
            }
            Stmt::Assign(Assign { root, segments, expr }) => {
                let root = self.builder.insert_identifer(root);
                if segments.is_empty() {
                    self.expr(expr);
                    self.builder.insert(Op::Store(root));
                } else {
                    let (last, rest) = segments.split_last().unwrap();
                    self.builder.insert(Op::Load(root));
                    for segment in rest {
                        match segment {
                            AssignSegment::Index(_) => todo!(),
                            AssignSegment::Field(field) => {
                                let field = self.builder.insert_identifer(field);
                                self.builder.insert(Op::LoadField(field));
                            }
                        }
                    }
                    match last {
                        AssignSegment::Field(field) => {
                            let field = self.builder.insert_identifer(field);
                            self.builder.insert(Op::StoreField(field));
                        }
                        AssignSegment::Index(_) => todo!(),
                    }
                }
            }
            Stmt::WhileLoop(WhileLoop { expr, body }) => {
                let start_label = self.builder.create_label();
                let end_label = self.builder.create_label();

                let prev_continue = self.continue_label.replace(start_label);
                let prev_break = self.break_label.replace(end_label);

                self.builder.insert_label(start_label);
                self.expr(expr);
                self.builder.insert(Op::CJump(end_label));
                self.gen_block(&body.stmts);
                self.builder.insert(Op::Jump(start_label));
                self.builder.insert_label(end_label);

                self.continue_label = prev_continue;
                self.break_label = prev_break;
            }
            Stmt::ForLoop(ForLoop { ident, iter, body }) => {
                let start_label = self.builder.create_label();
                let end_label = self.builder.create_label();

                let prev_continue = self.continue_label.replace(start_label);
                let prev_break = self.break_label.replace(end_label);

                self.expr(iter);
                self.builder.insert_label(start_label);
                self.builder.insert(Op::IterNext);
                self.builder.insert(Op::CJump(end_label));
                let ident = self.builder.insert_identifer(ident);
                self.builder.insert(Op::Store(ident));
                self.gen_block(&body.stmts);
                self.builder.insert(Op::Jump(start_label));
                self.builder.insert_label(end_label);

                self.continue_label = prev_continue;
                self.break_label = prev_break;
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
            Stmt::Continue => self.builder.insert(Op::Jump(self.continue_label.unwrap())),
            Stmt::Break => self.builder.insert(Op::Jump(self.break_label.unwrap())),
            Stmt::Return(Return(expr)) => {
                self.expr(expr);
                self.builder.insert(Op::Ret);
            }
            _ => todo!("{node:?}"),
        }
    }

    fn expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Literal(literal) => match literal {
                Literal::Bool(true) => self.builder.insert(Op::LoadTrue),
                Literal::Bool(false) => self.builder.insert(Op::LoadFalse),
                Literal::Char(char) => self.builder.insert(Op::LoadChar(*char)),
                Literal::Int(int) => self.builder.insert(Op::LoadInt(*int as _)),
                Literal::String(string) => {
                    let [ptr, len] = self.builder.insert_string(string);
                    self.builder.insert(Op::LoadString { ptr, len });
                }
                Literal::Ident(ident) => {
                    let key = self.builder.insert_identifer(ident);
                    self.builder.insert(Op::Load(key));
                }
            },
            Expr::Binary { op, exprs } => 'block: {
                let op = match op {
                    BinOp::Range => Op::Range,
                    BinOp::RangeInclusive => Op::RangeInclusive,
                    BinOp::Eq => Op::Eq,
                    BinOp::Mod => Op::Mod,
                    BinOp::Add => Op::Add,
                    BinOp::Neq => {
                        self.expr(&exprs[0]);
                        self.expr(&exprs[1]);
                        self.builder.insert(Op::Eq);
                        self.builder.insert(Op::Not);
                        break 'block;
                    }
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
            Expr::FieldAccess { expr, field } => {
                self.expr(expr);
                let field = self.builder.insert_identifer(field);
                self.builder.insert(Op::LoadField(field));
            }
            Expr::Index { expr, index } => {
                self.expr(expr);
                self.expr(index);
                self.builder.insert(Op::Index);
            }
            Expr::InitStruct { r#struct, fields } => {
                let _ = r#struct;
                self.builder.insert(Op::EmptyStruct);
                for StructInitField { ident, expr } in fields {
                    let ident = self.builder.insert_identifer(ident);
                    match expr {
                        Some(expr) => self.expr(expr),
                        None => self.builder.insert(Op::Load(ident)),
                    }
                    self.builder.insert(Op::StoreField(ident));
                }
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
