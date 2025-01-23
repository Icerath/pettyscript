use rustc_hash::FxHashSet;

use crate::{
    bytecode::{BytecodeBuilder, Op, StrIdent},
    parser::*,
    vm::Builtin,
};

pub fn codegen(ast: &[Stmt]) -> Vec<u8> {
    let mut codegen = Codegen::default();

    codegen.scopes.push(FxHashSet::default());
    codegen.insert_builtins();
    for node in ast {
        codegen.r#gen(node);
    }

    let main = codegen.builder.insert_identifer("main");
    if codegen.scopes.last().unwrap().contains(&main) {
        codegen.builder.insert(Op::Load(main, 0));
        codegen.builder.insert(Op::FnCall { numargs: 0 });
        codegen.builder.insert(Op::Pop);
    }

    codegen.finish()
}

#[derive(Default)]
struct Codegen {
    scopes: Vec<FxHashSet<StrIdent>>,
    builder: BytecodeBuilder,
    continue_label: Option<u32>,
    break_label: Option<u32>,
}

impl Codegen {
    fn insert_builtins(&mut self) {
        // TODO: Filter out unused identifiers
        let scope = self.scopes.last_mut().unwrap();
        for builtin in Builtin::ALL {
            let name = self.builder.insert_identifer(builtin.name());
            self.builder.insert(Op::LoadBuiltin(builtin));
            self.builder.insert(Op::Store(name, 0));
            scope.insert(name);
        }
    }
    fn gen_block(&mut self, ast: &[Stmt]) {
        self.scopes.push(FxHashSet::default());
        for node in ast {
            self.r#gen(node);
        }
        self.scopes.pop();
    }

    fn gen(&mut self, node: &Stmt) {
        match node {
            Stmt::Struct(_) => {}
            Stmt::Enum(Enum { ident, variants }) => {
                self.builder.insert(Op::EmptyStruct);

                for variant in variants {
                    let variant = self.builder.insert_identifer(variant);
                    self.builder.insert(Op::StoreEnumVariant(variant));
                }
                let name = self.builder.insert_identifer(ident);
                self.scopes.last_mut().unwrap().insert(name);
                self.builder.insert(Op::Store(name, self.current_scope()));
            }
            Stmt::Function(Function { ident, params, body }) => {
                let ident_key = self.builder.insert_identifer(ident);

                let function_start = self.builder.create_label();
                let function_end = self.builder.create_label();

                self.builder.insert(Op::CreateFunction { label: function_start });
                self.builder.insert(Op::Store(ident_key, self.current_scope()));
                self.scopes.last_mut().unwrap().insert(ident_key);

                self.builder.insert(Op::Jump(function_end));
                self.builder.insert_label(function_start);

                self.scopes.push(FxHashSet::default());
                for param in params {
                    let param = self.builder.insert_identifer(param);
                    self.scopes.last_mut().unwrap().insert(param);
                    self.builder.insert(Op::Store(param, self.current_scope()));
                }
                for stmt in &body.stmts {
                    self.r#gen(stmt);
                }
                self.scopes.pop();

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
                let newly_inserted = self.scopes.last_mut().unwrap().insert(ident);
                assert!(newly_inserted, "Variable shadowing not supported yet");
                self.builder.insert(Op::Store(ident, self.current_scope()));
            }
            Stmt::Assign(Assign { root, segments, expr }) => {
                let root = self.builder.insert_identifer(root);
                if segments.is_empty() {
                    self.expr(expr);
                    self.builder.insert(Op::Store(root, self.scope_of(root)));
                } else {
                    let (last, rest) = segments.split_last().unwrap();
                    self.builder.insert(Op::Load(root, self.scope_of(root)));
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
                            self.expr(expr);
                            let field = self.builder.insert_identifer(field);
                            self.builder.insert(Op::StoreField(field));
                        }
                        AssignSegment::Index(_) => todo!(),
                    }
                    self.builder.insert(Op::Pop);
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

                self.scopes.push(FxHashSet::default());

                let newly_inserted = self.scopes.last_mut().unwrap().insert(ident);
                assert!(newly_inserted);
                self.builder.insert(Op::Store(ident, self.current_scope()));

                for stmt in &body.stmts {
                    self.r#gen(stmt);
                }
                self.scopes.pop();

                self.builder.insert(Op::Jump(start_label));
                self.builder.insert_label(end_label);
                self.builder.insert(Op::Pop);

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
                    self.builder.insert(Op::Load(key, self.scope_of(key)));
                }
            },
            Expr::Binary { op, exprs } => 'block: {
                let op = match op {
                    BinOp::Range => Op::Range,
                    BinOp::RangeInclusive => Op::RangeInclusive,
                    BinOp::Eq => Op::Eq,
                    BinOp::Mod => Op::Mod,
                    BinOp::Add => Op::Add,
                    BinOp::Less => Op::Less,
                    BinOp::Greater => Op::Greater,
                    BinOp::Neq => {
                        self.expr(&exprs[0]);
                        self.expr(&exprs[1]);
                        self.builder.insert(Op::Eq);
                        self.builder.insert(Op::Not);
                        break 'block;
                    }
                    BinOp::And => {
                        let end_label = self.builder.create_label();
                        self.expr(&exprs[0]);
                        self.builder.insert(Op::Dup);
                        self.builder.insert(Op::CJump(end_label));
                        self.builder.insert(Op::Pop);
                        self.expr(&exprs[1]);
                        self.builder.insert_label(end_label);
                        break 'block;
                    }
                    BinOp::Or => {
                        let end_label = self.builder.create_label();
                        self.expr(&exprs[0]);
                        self.builder.insert(Op::Dup);
                        self.builder.insert(Op::Not);
                        self.builder.insert(Op::CJump(end_label));
                        self.builder.insert(Op::Pop);
                        self.expr(&exprs[1]);
                        self.builder.insert_label(end_label);
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
                        None => self.builder.insert(Op::Load(ident, self.scope_of(ident))),
                    }
                    self.builder.insert(Op::StoreField(ident));
                }
            }
            _ => todo!("{expr:?}"),
        }
    }

    fn scope_of(&self, ident: StrIdent) -> u32 {
        self.scopes
            .iter()
            .rposition(|x| x.contains(&ident))
            .unwrap_or_else(|| panic!("ident: '{}' not found", self.builder.read_identifer(ident)))
            as u32
    }
    fn current_scope(&self) -> u32 {
        self.scopes.len() as u32 - 1
    }

    fn finish(self) -> Vec<u8> {
        self.builder.finish()
    }
}
