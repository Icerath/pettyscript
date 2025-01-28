use std::rc::Rc;

use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    builtints::Builtin,
    bytecode::{BytecodeBuilder, Op},
    parser::*,
};

pub fn codegen(ast: &[Stmt]) -> Vec<u8> {
    let mut codegen = Codegen::default();

    codegen.scopes.push(FunctionScope::default());
    codegen.insert_builtins();
    for node in ast {
        codegen.r#gen(node);
    }

    if let Some(&offset) = codegen.scopes.last().unwrap().variables.get("main") {
        codegen.builder.insert(Op::Load(offset));
        codegen.builder.insert(Op::FnCall { numargs: 0 });
        codegen.builder.insert(Op::Pop);
    }
    codegen.scopes.pop().unwrap();

    codegen.finish()
}

#[derive(Debug, PartialEq)]
pub struct FnSig {
    ret: Type,
    args: [Type],
}

#[derive(Debug, PartialEq, Clone)]
pub enum Type {
    Null,
    Range,
    RangeInclusive,
    Bool,
    Char,
    Int,
    Str,
    Struct { name: &'static str, fields: Rc<FxHashMap<&'static str, Type>> },
    Enum { name: &'static str, fields: Rc<FxHashSet<&'static str>> },
    Function(Rc<FnSig>),
}

#[derive(Default)]
struct FunctionScope {
    variables: FxHashMap<&'static str, u32>,
    var_types: FxHashMap<&'static str, Option<Type>>,
    named_types: FxHashMap<&'static str, Type>,
    nfor_loops: usize,
}

#[derive(Default)]
struct Codegen {
    scopes: Vec<FunctionScope>,
    builder: BytecodeBuilder,
    continue_label: Option<u32>,
    break_label: Option<u32>,
}

impl Codegen {
    fn insert_builtins(&mut self) {
        for builtin in Builtin::ALL {
            // TODO: each buitlin should have a type.
            self.write_ident_offset(builtin.name(), None);
        }
        let scope = self.scopes.first_mut().unwrap();
        // FIXME: Should these types be inserted into the interner?
        scope.named_types.insert("int", Type::Int);
        scope.named_types.insert("str", Type::Str);
        scope.named_types.insert("bool", Type::Bool);
        scope.named_types.insert("char", Type::Char);
        scope.named_types.insert("null", Type::Null);
    }

    fn gen_block(&mut self, ast: &[Stmt]) {
        for node in ast {
            self.r#gen(node);
        }
    }

    fn write_ident_offset(&mut self, ident: &'static str, ty: Option<Type>) -> u32 {
        let offset = self.scopes.last().unwrap().variables.len() as u32;
        let newly_inserted = self.scopes.last_mut().unwrap().variables.insert(ident, offset);
        self.scopes.last_mut().unwrap().var_types.insert(ident, ty);
        assert!(newly_inserted.is_none());
        offset
    }

    fn r#gen(&mut self, node: &Stmt) {
        match node {
            Stmt::Struct(r#struct) => {
                let mut fields = FxHashMap::default();
                for &(field, typ) in &r#struct.fields {
                    fields.insert(field, self.load_name_type(typ).unwrap());
                }
                let typ = Type::Struct { name: r#struct.ident, fields: Rc::new(fields) };
                self.scopes.last_mut().unwrap().named_types.insert(r#struct.ident, typ);
            }
            Stmt::Enum(Enum { ident, variants }) => {
                let typ =
                    Type::Enum { name: ident, fields: Rc::new(variants.iter().copied().collect()) };
                self.scopes.last_mut().unwrap().named_types.insert(ident, typ);

                self.builder.insert(Op::EmptyStruct);

                for variant in variants {
                    let variant = self.builder.insert_identifer(variant);
                    self.builder.insert(Op::StoreEnumVariant(variant));
                }

                let offset = self.write_ident_offset(ident, None);
                self.builder.insert(Op::Store(offset));
            }

            Stmt::Function(Function { ident, params, ret_type, body }) => {
                let _ = ret_type;
                let function_start = self.builder.create_label();
                let function_end = self.builder.create_label();

                let offset = self.write_ident_offset(ident, None);
                self.builder.insert(Op::CreateFunction);
                self.builder.insert(Op::Store(offset));
                self.builder.insert(Op::Jump(function_end));
                self.builder.insert_label(function_start);

                self.scopes.push(FunctionScope::default());

                for param in params {
                    let offset = self.write_ident_offset(param.0, None);
                    self.builder.insert(Op::Store(offset));
                }
                for stmt in &body.stmts {
                    self.r#gen(stmt);
                }
                self.scopes.pop().unwrap();

                self.builder.insert(Op::LoadNull);
                self.builder.insert(Op::Ret);

                self.builder.insert_label(function_end);
            }
            Stmt::Let(VarDecl { ident, typ, expr }) | Stmt::Const(VarDecl { ident, typ, expr }) => {
                let expected = typ.map(|typ| {
                    self.load_name_type(typ).unwrap_or_else(|| panic!("Unknown type: {typ:?}"))
                });
                let ty = match expr {
                    Some(expr) => self.expr(expr),
                    None => {
                        let expected = expected.clone().unwrap();
                        let op = match expected {
                            Type::Null => Op::LoadNull,
                            Type::Int => Op::LoadInt(0),
                            Type::Str => Op::LoadString { ptr: 0, len: 0 },
                            _ => todo!("{expected:?}"),
                        };
                        self.builder.insert(op);
                        Some(expected)
                    }
                };
                if let (Some(ty), Some(expected)) = (&ty, &expected) {
                    assert_eq!(ty, expected);
                }
                let offset = self.write_ident_offset(ident, ty);
                self.builder.insert(Op::Store(offset));
            }
            Stmt::Assign(Assign { root, segments, expr }) => {
                if segments.is_empty() {
                    let ty = self.expr(expr);
                    let expected = self.load_var_type(root);
                    if let (Some(ty), Some(expected)) = (ty, expected) {
                        // FIXME: Special case null until explicit types are properly supported to allow late initialization.
                        if *expected != Type::Null && *expected != ty {
                            panic!("Type Error: expected {expected:?}, Got: {ty:?}");
                        }
                    }
                    self.store(root);
                } else {
                    let (last, rest) = segments.split_last().unwrap();
                    self.load(root);
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
                let typ = self.expr(expr);
                match typ {
                    Some(Type::Bool) => {}
                    Some(other) => panic!("Cannot use type: {other:?} in while loop"),
                    None => {}
                }
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

                let iter = self.expr(iter);
                let ident_typ = match &iter {
                    Some(Type::Range | Type::RangeInclusive) => Some(Type::Int),
                    None => None,
                    _ => panic!(),
                };

                self.builder.insert_label(start_label);
                let iter_op = match iter {
                    Some(Type::Range) => Op::IterRange,
                    Some(Type::RangeInclusive) => Op::IterRangeInclusive,
                    Some(typ) => panic!("{typ:?}"),
                    None => Op::IterNext,
                };
                self.builder.insert(iter_op);
                self.builder.insert(Op::CJump(end_label));

                self.scopes.last_mut().unwrap().var_types.insert(ident, ident_typ);
                let offset = self.write_ident_offset(ident, None);
                self.builder.insert(Op::Store(offset));

                self.scopes.last_mut().unwrap().nfor_loops += 1;

                for stmt in &body.stmts {
                    self.r#gen(stmt);
                }

                self.scopes.last_mut().unwrap().nfor_loops -= 1;

                self.builder.insert(Op::Jump(start_label));
                self.builder.insert_label(end_label);
                self.builder.insert(Op::Pop);

                self.continue_label = prev_continue;
                self.break_label = prev_break;
            }
            Stmt::IfChain(IfChain { first, else_ifs, r#else }) => {
                let typ = self.expr(&first.condition);
                match typ {
                    Some(Type::Bool) | None => {}
                    Some(other) => panic!("Cannot use type {other:?} in if stmts"),
                }
                let final_end_label = self.builder.create_label();
                let mut next_label = self.builder.create_label();
                self.builder.insert(Op::CJump(next_label));
                self.gen_block(&first.body.stmts);
                self.builder.insert(Op::Jump(final_end_label));
                for elseif in else_ifs {
                    self.builder.insert_label(next_label);
                    let typ = self.expr(&elseif.condition);
                    match typ {
                        Some(Type::Bool) | None => {}
                        Some(other) => panic!("Cannot use type {other:?} in if stmts"),
                    }
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
                if let Some(expr) = expr {
                    self.expr(expr);
                } else {
                    self.builder.insert(Op::LoadNull);
                }
                for _ in 0..self.scopes.last().unwrap().nfor_loops {
                    self.builder.insert(Op::Pop);
                }
                self.builder.insert(Op::Ret);
            }
            _ => todo!("{node:?}"),
        }
    }

    fn store(&mut self, ident: &'static str) {
        match self.scopes.last().unwrap().variables.get(ident) {
            Some(&offset) => self.builder.insert(Op::Store(offset)),
            None => panic!(),
        };
    }

    fn load_var_type(&self, ident: &'static str) -> Option<&Type> {
        match self.scopes.last().unwrap().var_types.get(ident) {
            Some(ty) => ty.as_ref(),
            None => {
                let scope = self.scopes.first().unwrap();
                scope.var_types.get(ident).unwrap().as_ref()
            }
        }
    }

    fn load_name_type(&self, type_name: &'static str) -> Option<Type> {
        match self.scopes.last().unwrap().named_types.get(type_name) {
            Some(typ) => Some(typ.clone()),
            None => self.scopes.first().unwrap().named_types.get(type_name).cloned(),
        }
    }

    fn load(&mut self, ident: &'static str) -> Option<Type> {
        match self.scopes.last().unwrap().variables.get(ident) {
            Some(&offset) => {
                self.builder.insert(Op::Load(offset));
                self.scopes.last().unwrap().var_types.get(ident).unwrap().clone()
            }
            None => {
                let scope = self.scopes.first().unwrap();
                let offset =
                    *scope.variables.get(ident).unwrap_or_else(|| panic!("Unknown ident: {ident}"));
                self.builder.insert(Op::LoadGlobal(offset));
                scope.var_types.get(ident).unwrap().clone()
            }
        }
    }

    fn expr(&mut self, expr: &Expr) -> Option<Type> {
        let ty = match expr {
            Expr::Literal(literal) => match literal {
                Literal::Bool(true) => {
                    self.builder.insert(Op::LoadTrue);
                    Type::Bool
                }
                Literal::Bool(false) => {
                    self.builder.insert(Op::LoadFalse);
                    Type::Bool
                }
                Literal::Char(char) => {
                    self.builder.insert(Op::LoadChar(*char));
                    Type::Char
                }
                Literal::Int(int) => {
                    self.builder.insert(Op::LoadInt(*int));
                    Type::Int
                }
                Literal::String(string) => {
                    let [ptr, len] = self.builder.insert_string(string);
                    self.builder.insert(Op::LoadString { ptr, len });
                    Type::Str
                }
                Literal::Ident(ident) => return self.load(ident),
            },
            Expr::Binary { op, exprs } => {
                return 'block: {
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
                            break 'block Some(Type::Bool);
                        }
                        BinOp::And => {
                            let end_label = self.builder.create_label();
                            self.expr(&exprs[0]);
                            self.builder.insert(Op::Dup);
                            self.builder.insert(Op::CJump(end_label));
                            self.builder.insert(Op::Pop);
                            self.expr(&exprs[1]);
                            self.builder.insert_label(end_label);
                            break 'block Some(Type::Bool);
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
                            break 'block Some(Type::Bool);
                        }
                        _ => todo!("{op:?}"),
                    };
                    let lhs_ty = self.expr(&exprs[0]);
                    let rhs_ty = self.expr(&exprs[1]);
                    let Some((lhs_ty, rhs_ty)) = lhs_ty.and_then(|l| rhs_ty.map(|r| (l, r))) else {
                        self.builder.insert(op);
                        return None;
                    };
                    let typ = match (lhs_ty, rhs_ty, op) {
                        (_, _, Op::Eq | Op::Less | Op::Greater) => Some(Type::Bool),
                        (Type::Int, Type::Int, Op::Range) => Some(Type::Range),
                        (Type::Int, Type::Int, Op::RangeInclusive) => Some(Type::RangeInclusive),
                        (_, _, Op::Range | Op::RangeInclusive) => panic!(),
                        // FIXME: This catchall might have false positives
                        (lhs, rhs, _) if lhs == rhs => Some(lhs),
                        (lhs, rhs, op) => panic!("{op:?}: {lhs:?} - {rhs:?}"),
                    };
                    if op == Op::Add && typ == Some(Type::Int) {
                        self.builder.insert(Op::AddInt);
                    } else {
                        self.builder.insert(op);
                    }
                    typ
                };
            }
            Expr::FnCall { function, args } => {
                for arg in args {
                    self.expr(arg);
                }
                self.expr(function);
                self.builder.insert(Op::FnCall { numargs: args.len() as u8 });
                return None;
            }
            Expr::FieldAccess { expr, field } => {
                self.expr(expr);
                let field = self.builder.insert_identifer(field);
                self.builder.insert(Op::LoadField(field));
                return None;
            }
            Expr::Index { expr, index } => {
                self.expr(expr);
                self.expr(index);
                self.builder.insert(Op::Index);
                return None;
            }
            Expr::InitStruct { ident, fields } => {
                let _ = ident;
                self.builder.insert(Op::EmptyStruct);
                for StructInitField { ident, expr } in fields {
                    let ty = match expr {
                        Some(expr) => self.expr(expr),
                        None => self.load(ident),
                    };
                    let ident = self.builder.insert_identifer(ident);
                    self.builder.insert(Op::StoreField(ident));
                }
                return None;
            }
            Expr::Array(array) => {
                self.builder.insert(Op::CreateArray);
                for expr in array {
                    self.expr(expr);
                    self.builder.insert(Op::ArrayPush);
                }
                return None;
            }
            Expr::Unary { op, expr } => {
                let typ = self.expr(expr);
                if let Some(typ) = &typ {
                    if *op == UnaryOp::Not && *typ != Type::Bool {
                        panic!("Cannot use ! operator on {typ:?}");
                    }
                    if *op == UnaryOp::Neg && *typ != Type::Int {
                        panic!("Cannot use - operator on {typ:?}");
                    }
                }
                match op {
                    UnaryOp::Not => self.builder.insert(Op::Not),
                    UnaryOp::Neg => self.builder.insert(Op::Neg),
                }
                return typ;
            }
        };
        Some(ty)
    }

    fn finish(self) -> Vec<u8> {
        self.builder.finish()
    }
}
