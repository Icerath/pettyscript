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
    args: Box<[Type]>,
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
    Map { key: Rc<IncompleteType>, value: Rc<IncompleteType> },
    Array(Rc<IncompleteType>),
    Function(Rc<FnSig>),
}
impl Type {
    pub fn matches(&self, other: &Type) -> bool {
        if self == other {
            return true;
        }
        match (self, other) {
            (Self::Array(lhs), Self::Array(rhs)) => lhs.is_complete() || rhs.is_complete(),
            (Self::Map { key: lk, value: lv }, Self::Map { key: rk, value: rv }) => {
                (lk.is_complete() || rk.is_complete()) && (lv.is_complete() || rv.is_complete())
            }
            _ => false,
        }
    }
}

#[derive(Debug, PartialEq, Clone)]
pub enum IncompleteType {
    Complete(Type),
    Generic,
}

impl IncompleteType {
    pub fn is_complete(&self) -> bool {
        matches!(self, Self::Complete(_))
    }

    #[track_caller]
    pub fn unwrap_complete(&self) -> Type {
        match self {
            Self::Complete(typ) => typ.clone(),
            Self::Generic => panic!(),
        }
    }
}

#[derive(Default, Debug)]
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

fn builtin_type(builtin: Builtin) -> Option<Type> {
    Some(Type::Function(Rc::new(match builtin {
        Builtin::Assert => FnSig { ret: Type::Bool, args: [Type::Bool].into() },
        Builtin::Exit => FnSig { ret: Type::Null, args: [Type::Int].into() }, // FIXME: Return never type.
        Builtin::Println => FnSig { ret: Type::Null, args: [Type::Str].into() },
        Builtin::ReadFile => FnSig { ret: Type::Str, args: [Type::Str].into() },
    })))
}

impl Codegen {
    fn insert_builtins(&mut self) {
        for builtin in Builtin::ALL {
            self.write_ident_offset(builtin.name(), builtin_type(builtin));
        }
        let scope = self.scopes.first_mut().unwrap();
        // FIXME: Should these types be inserted into the interner?
        scope.named_types.insert("int", Type::Int);
        scope.named_types.insert("str", Type::Str);
        scope.named_types.insert("bool", Type::Bool);
        scope.named_types.insert("char", Type::Char);
        scope.named_types.insert("null", Type::Null);
        scope.named_types.insert("array", Type::Array(Rc::new(IncompleteType::Generic)));
        scope.named_types.insert("map", Type::Map {
            key: Rc::new(IncompleteType::Generic),
            value: Rc::new(IncompleteType::Generic),
        });
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
                for (field, typ) in &r#struct.fields {
                    fields.insert(*field, self.load_explicit_type(typ).unwrap());
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
                let function_start = self.builder.create_label();
                let function_end = self.builder.create_label();

                let ret = ret_type
                    .as_ref()
                    .map_or(Type::Null, |typ| self.load_explicit_type(typ).unwrap());
                let mut args = vec![];
                for (_ident, typ) in params {
                    let typ = self.load_explicit_type(typ).unwrap();
                    args.push(typ);
                }
                let typ = Type::Function(Rc::new(FnSig { ret, args: args.into() }));

                self.scopes.last_mut().unwrap().var_types.insert(ident, Some(typ));
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
                let expected = typ.as_ref().map(|typ| {
                    self.load_explicit_type(typ).unwrap_or_else(|| panic!("Unknown type: {typ:?}"))
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
                    assert!(ty.matches(expected));
                }
                let ty = if expected.is_some() { expected } else { ty };
                let offset = self.write_ident_offset(ident, ty);
                self.builder.insert(Op::Store(offset));
            }
            Stmt::Assign(Assign { root, segments, expr }) => {
                if segments.is_empty() {
                    let ty = self.expr(expr);
                    let expected = self.load_var_type(root);
                    if let (Some(ty), Some(expected)) = (ty, expected) {
                        if *expected != ty {
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

                let offset = self.write_ident_offset(ident, ident_typ);
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

    fn load_explicit_type(&self, explicit_typ: &ExplicitType) -> Option<Type> {
        let typ = self.load_name_type(explicit_typ.ident)?;
        Some(match typ {
            Type::Array(typ) if *typ == IncompleteType::Generic => {
                assert_eq!(explicit_typ.generics.len(), 1);
                Type::Array(Rc::new(IncompleteType::Complete(
                    self.load_explicit_type(&explicit_typ.generics[0])?,
                )))
            }
            Type::Map { key, value } if !key.is_complete() || !value.is_complete() => {
                assert_eq!(explicit_typ.generics.len(), 2);
                Type::Map {
                    key: Rc::new(IncompleteType::Complete(
                        self.load_explicit_type(&explicit_typ.generics[0])?,
                    )),
                    value: Rc::new(IncompleteType::Complete(
                        self.load_explicit_type(&explicit_typ.generics[1])?,
                    )),
                }
            }
            other => {
                assert_eq!(explicit_typ.generics.len(), 0);
                other
            }
        })
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
                Literal::Map(map) => {
                    self.builder.insert(Op::CreateMap);
                    if map.is_empty() {
                        return Some(Type::Map {
                            key: Rc::new(IncompleteType::Generic),
                            value: Rc::new(IncompleteType::Generic),
                        });
                    }
                    let mut entries = map.iter();
                    let [key, val] = entries.next().unwrap();
                    let key_typ = self.expr(key).unwrap();
                    let val_typ = self.expr(val).unwrap();
                    self.builder.insert(Op::InsertMap);

                    for [key, val] in entries {
                        assert_eq!(self.expr(key).unwrap(), key_typ);
                        assert_eq!(self.expr(val).unwrap(), val_typ);
                        self.builder.insert(Op::InsertMap);
                    }

                    Type::Map {
                        key: Rc::new(IncompleteType::Complete(key_typ)),
                        value: Rc::new(IncompleteType::Complete(val_typ)),
                    }
                }
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
                Literal::FString(fstring) => {
                    for (str, expr) in &fstring.segments {
                        let [ptr, len] = self.builder.insert_string(str);
                        self.builder.insert(Op::LoadString { ptr, len });
                        self.expr(expr);
                    }
                    let [ptr, len] = self.builder.insert_string(fstring.remaining);
                    self.builder.insert(Op::LoadString { ptr, len });
                    self.builder
                        .insert(Op::BuildFstr { num_segments: fstring.segments.len() as u16 });
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
                let mut arg_types = vec![];
                for arg in args {
                    arg_types.push(self.expr(arg));
                }
                let typ = self.expr(function);
                let ret_type = match typ {
                    Some(Type::Function(fn_type)) => {
                        assert_eq!(fn_type.args.len(), arg_types.len(), "{function:?}");
                        for (arg_ty, param_ty) in arg_types.iter().zip(&fn_type.args) {
                            if arg_ty.is_some() {
                                assert_eq!(arg_ty.as_ref(), Some(param_ty));
                            }
                        }
                        Some(fn_type.ret.clone())
                    }
                    Some(other) => panic!("Cannot call {other:?}"),
                    None => None,
                };
                self.builder.insert(Op::FnCall { numargs: args.len() as u8 });
                return ret_type;
            }
            Expr::FieldAccess { expr, field } => {
                let typ = self.expr(expr);
                let field_type = typ.and_then(|typ| self.field_type(typ, field));
                let field = self.builder.insert_identifer(field);
                self.builder.insert(Op::LoadField(field));
                return field_type;
            }
            Expr::Index { expr, index } => {
                let container_typ = self.expr(expr);
                let index_typ = self.expr(index);
                self.builder.insert(Op::Index);
                return self.index_type(container_typ?, index_typ?);
            }
            Expr::InitStruct { ident, fields } => {
                let struct_type = self.load_name_type(ident).unwrap();
                let Type::Struct { name: _, fields: type_fields } = &struct_type else { panic!() };
                self.builder.insert(Op::EmptyStruct);
                for StructInitField { ident, expr } in fields {
                    assert!(type_fields.contains_key(ident));
                    let typ = match expr {
                        Some(expr) => self.expr(expr),
                        None => self.load(ident),
                    };
                    if let Some(typ) = typ {
                        assert_eq!(type_fields.get(ident).unwrap(), &typ);
                    }
                    let ident = self.builder.insert_identifer(ident);
                    self.builder.insert(Op::StoreField(ident));
                }
                struct_type
            }
            Expr::Array(array) => 'block: {
                self.builder.insert(Op::CreateArray);

                if array.is_empty() {
                    break 'block Type::Array(Rc::new(IncompleteType::Generic));
                }
                let mut array_iter = array.iter();
                let typ = self.expr(array_iter.next().unwrap()).unwrap();
                self.builder.insert(Op::ArrayPush);
                for expr in array_iter {
                    let next_typ = self.expr(expr);
                    assert_eq!(next_typ.as_ref(), Some(&typ));
                    self.builder.insert(Op::ArrayPush);
                }
                Type::Array(Rc::new(IncompleteType::Complete(typ)))
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

    fn index_type(&self, container: Type, index: Type) -> Option<Type> {
        Some(match container {
            Type::Str => match index {
                Type::Range => Type::Str,
                Type::Int => Type::Char,
                _ => panic!("Cannot index str with type: {index:?}"),
            },
            Type::Array(of) => match index {
                Type::Int => (*of).clone().unwrap_complete(),
                _ => panic!("Cannot index Array({of:?}) with type: {index:?}"),
            },
            _ => panic!("Cannot index {container:?}"),
        })
    }

    fn field_type(&self, typ: Type, field: &str) -> Option<Type> {
        Some(match typ {
            Type::Enum { fields, .. } if fields.contains(field) => return None,
            Type::Str => match field {
                "len" => Type::Int,
                "trim" => Type::Function(Rc::new(FnSig { ret: Type::Str, args: [].into() })),
                "starts_with" => {
                    Type::Function(Rc::new(FnSig { ret: Type::Bool, args: [Type::Str].into() }))
                }
                "is_digit" => Type::Function(Rc::new(FnSig { ret: Type::Bool, args: [].into() })),
                "is_alphabetic" => {
                    Type::Function(Rc::new(FnSig { ret: Type::Bool, args: [].into() }))
                }
                _ => panic!("type str does not contain field: {field}"),
            },
            Type::Map { key, value } => match field {
                "insert" => Type::Function(Rc::new(FnSig {
                    ret: Type::Null,
                    args: [key.unwrap_complete(), value.unwrap_complete()].into(),
                })),
                "remove" => Type::Function(Rc::new(FnSig {
                    ret: Type::Null,
                    args: [key.unwrap_complete()].into(),
                })),
                "get" => Type::Function(Rc::new(FnSig {
                    ret: value.unwrap_complete(),
                    args: [key.unwrap_complete()].into(),
                })),
                _ => panic!("type map does not contain field: {field}"),
            },
            Type::Struct { name, fields } => match fields.get(field) {
                Some(field_type) => field_type.clone(),
                None => panic!("struct {name} does not contain field: {field}"),
            },
            Type::Array(of) => match field {
                "pop" => Type::Function(Rc::new(FnSig {
                    ret: (*of).clone().unwrap_complete(),
                    args: [].into(),
                })),
                "push" => Type::Function(Rc::new(FnSig {
                    ret: Type::Null,
                    args: [(*of).clone().unwrap_complete()].into(),
                })),
                _ => panic!("type Array({of:?}) does not contain field: {field}"),
            },
            _ => panic!("type {typ:?} does not contain field: {field}"),
        })
    }

    fn finish(self) -> Vec<u8> {
        self.builder.finish()
    }
}
