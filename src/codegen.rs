use std::{
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use logos::Span;
use miette::{LabeledSpan, Result};
use rustc_hash::FxHashMap;

use crate::{
    builtints::{Builtin, BuiltinField, MethodBuiltin},
    bytecode::{BytecodeBuilder, Op, StrIdent},
    errors,
    parser::*,
};

pub fn codegen(ast: Ast) -> Result<Vec<u8>> {
    let mut codegen = Codegen { src: ast.src, ..Codegen::default() };
    codegen.scopes.push(FunctionScope::new(Type::Null));

    codegen.insert_builtins();
    for node in ast.body {
        codegen.r#gen(node)?;
    }

    if let Some(var) = codegen.scopes.last().unwrap().variables.get("main") {
        codegen.builder.insert(Op::Load(var.offset));
        codegen.builder.insert(Op::FnCall);
    }
    let last_scope = codegen.scopes.pop().unwrap();
    codegen.builder.set_global_stack_size(last_scope.variables.len() as u32);

    Ok(codegen.finish())
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
    Struct { name: &'static str, fields: Rc<FxHashMap<&'static str, (u32, Type)>> },
    Enum { name: &'static str, fields: Rc<FxHashMap<&'static str, u32>>, id: u32 },
    EnumVariant { id: u32 },
    Map { key: Rc<Type>, value: Rc<Type> },
    Array(Rc<Type>),
    Tuple(Rc<[Type]>),
    Function(Rc<FnSig>),
    Unknown,
}

impl Type {
    fn is_fully_known(&self) -> bool {
        match self {
            Self::Array(typ) => typ.is_fully_known(),
            Self::Map { key, value } => key.is_fully_known() && value.is_fully_known(),
            Self::Unknown => false,
            _ => true,
        }
    }

    fn try_combine(&self, other: &Type) -> Option<Type> {
        if self == other {
            return Some(self.clone());
        }
        Some(match (self, other) {
            (Self::Array(lhs), Self::Array(rhs)) => Self::Array(Rc::new(lhs.try_combine(rhs)?)),
            (Self::Map { key: lk, value: lv }, Self::Map { key: rk, value: rv }) => {
                Self::Map { key: Rc::new(lk.try_combine(rk)?), value: Rc::new(lv.try_combine(rv)?) }
            }
            (Self::Tuple(lhs), Self::Tuple(rhs)) => {
                assert_eq!(lhs.len(), rhs.len());
                Self::Tuple(
                    lhs.iter()
                        .zip(&**rhs)
                        .map(|(lhs, rhs)| lhs.try_combine(rhs))
                        .collect::<Option<_>>()?,
                )
            }
            (Self::Unknown, typ) | (typ, Self::Unknown) => typ.clone(),
            _ => return None,
        })
    }

    pub fn is_zst(&self) -> bool {
        // TODO: Empty structs should probably also be zsts
        matches!(self, Self::Null)
    }
}

trait RcExt<T: Clone> {
    fn clone_inner(&self) -> T;
}

impl<T: Clone> RcExt<T> for Rc<T> {
    fn clone_inner(&self) -> T {
        (**self).clone()
    }
}

enum LoadMethod {
    Builtin(MethodBuiltin),
    //StructMethod(u32),
}

enum LoadField {
    Builtin(BuiltinField),
    StructField(u32),
    EnumVariant(StrIdent),
    ZstField,
}

#[derive(Debug)]
struct Variable {
    offset: u32,
    typ: Type,
    is_const: bool,
}

#[derive(Debug)]
struct FunctionScope {
    ret: Type,
    variables: FxHashMap<&'static str, Variable>,
    named_types: FxHashMap<&'static str, Type>,
}

impl FunctionScope {
    fn new(ret: Type) -> Self {
        Self { ret, variables: Default::default(), named_types: Default::default() }
    }
}

#[derive(Default)]
struct Codegen<'src> {
    src: &'src str,
    scopes: Vec<FunctionScope>,
    builder: BytecodeBuilder,
    continue_label: Option<u32>,
    break_label: Option<u32>,
}

fn builtin_type(builtin: Builtin) -> Type {
    Type::Function(Rc::new(match builtin {
        Builtin::ParseInt => FnSig { ret: Type::Int, args: [Type::Str].into() },
        Builtin::Assert => FnSig { ret: Type::Bool, args: [Type::Bool].into() },
        Builtin::Exit => FnSig { ret: Type::Null, args: [Type::Int].into() }, // FIXME: Return never type.
        Builtin::Println => FnSig { ret: Type::Null, args: [Type::Str].into() },
        Builtin::ReadFile => FnSig { ret: Type::Str, args: [Type::Str].into() },
    }))
}

impl Codegen<'_> {
    fn insert_builtins(&mut self) {
        let scope = self.scopes.first_mut().unwrap();
        for builtin in Builtin::ALL {
            let offset = scope.variables.len() as u32;
            let builtin_var = Variable { offset, typ: builtin_type(builtin), is_const: true };
            scope.variables.insert(builtin.name(), builtin_var);
        }
        scope.variables.insert("null", Variable { offset: 0, typ: Type::Null, is_const: true });
        // FIXME: Should these types be inserted into the interner?
        scope.named_types.insert("int", Type::Int);
        scope.named_types.insert("str", Type::Str);
        scope.named_types.insert("bool", Type::Bool);
        scope.named_types.insert("char", Type::Char);
        scope.named_types.insert("null", Type::Null);
        scope.named_types.insert("array", Type::Array(Rc::new(Type::Unknown)));
        scope.named_types.insert("tuple", Type::Tuple(Rc::new([])));
        scope.named_types.insert("map", Type::Map {
            key: Rc::new(Type::Unknown),
            value: Rc::new(Type::Unknown),
        });
    }

    fn gen_block(&mut self, ast: &[Spanned<Stmt>]) -> Result<()> {
        for node in ast {
            self.r#gen(node)?;
        }
        Ok(())
    }

    fn store_new(&mut self, ident: Ident, typ: Type, is_const: bool, span: Span) -> Result<()> {
        if !typ.is_fully_known() {
            let span = LabeledSpan::at(span, "");
            return Err(miette::miette!(
                labels = [span],
                help = format!("consider giving `{ident}` an explicit type"),
                "type annotation needed",
            )
            .with_source_code(self.src.to_string()));
        }
        assert!(typ.is_fully_known());
        if typ.is_zst() {
            if ident != "_" {
                let _ = self.write_ident_offset(ident, typ, is_const);
            }
            return Ok(());
        }
        if ident == "_" {
            self.builder.insert(Op::Pop);
        } else {
            let offset = self.write_ident_offset(ident, typ, is_const);
            self.builder.insert(Op::Store(offset));
        }
        Ok(())
    }

    fn write_ident_offset(&mut self, ident: &'static str, typ: Type, is_const: bool) -> u32 {
        let offset = self.scopes.last().unwrap().variables.len() as u32;
        let newly_inserted = self.scopes.last_mut().unwrap().variables.insert(ident, Variable {
            offset,
            typ,
            is_const,
        });
        assert!(newly_inserted.is_none());
        offset
    }

    fn r#gen(&mut self, node: &Spanned<Stmt>) -> Result<()> {
        match &node.inner {
            Stmt::Struct(r#struct) => {
                let mut fields = FxHashMap::default();
                for (i, (field, typ)) in r#struct.fields.iter().enumerate() {
                    fields.insert(**field, (i as u32, self.load_explicit_type(typ).unwrap()));
                }
                let typ = Type::Struct { name: *r#struct.ident, fields: Rc::new(fields) };
                self.scopes.last_mut().unwrap().named_types.insert(*r#struct.ident, typ);
            }
            Stmt::Enum(Enum { ident, variants }) => {
                // Each enum it of a different type
                static COUNTER: AtomicU32 = AtomicU32::new(0);
                let id = COUNTER.fetch_add(1, Ordering::Relaxed);
                let typ = Type::Enum {
                    name: ident,
                    fields: Rc::new(
                        variants.iter().map(|span| &span.inner).copied().zip(0u32..).collect(),
                    ),
                    id,
                };
                self.scopes.last_mut().unwrap().named_types.insert(ident, Type::EnumVariant { id });
                self.write_ident_offset(ident, typ, true);
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
                let typ = Type::Function(Rc::new(FnSig { ret: ret.clone(), args: args.into() }));

                let offset = self.write_ident_offset(ident, typ.clone(), true);
                let set_stack_size = self.builder.create_function();
                self.builder.insert(Op::Store(offset));
                self.builder.insert(Op::Jump(function_end));
                self.builder.insert_label(function_start);

                self.scopes.push(FunctionScope::new(ret.clone()));

                for (ident, explicit_typ) in params {
                    let typ = self.load_explicit_type(explicit_typ).unwrap();
                    self.store_new(ident, typ, false, ident.span.clone())?;
                }
                for stmt in &body.stmts {
                    self.r#gen(stmt)?;
                }
                let num_scope_vars = self.scopes.last().unwrap().variables.len();
                // TODO: Remove extra space for ZSTs
                self.builder.set_function_stack_size(set_stack_size, num_scope_vars as u16);
                self.scopes.pop().unwrap();

                if ret == Type::Null {
                    self.builder.insert(Op::Ret);
                } else {
                    // FIXME: Instead produce a compile error when this is possible
                    self.builder.insert(Op::Abort);
                }

                self.builder.insert_label(function_end);
            }
            Stmt::Let(var_decl) => self.var_decl(var_decl, false)?,
            Stmt::Const(var_decl) => self.var_decl(var_decl, true)?,
            Stmt::Assign(Assign { root, segments, expr }) => {
                if segments.is_empty() {
                    let ty = self.expr(expr)?;
                    let expected = self.load_var_type(root);
                    if *expected != ty {
                        panic!("Type Error: expected {expected:?}, Got: {ty:?}");
                    }
                    self.store(root);
                } else {
                    let (last, rest) = segments.split_last().unwrap();
                    let mut segment_type = self.load(root.clone())?;
                    for segment in rest {
                        match segment {
                            AssignSegment::Index(_) => todo!(),
                            AssignSegment::Field(field) => {
                                let (load_field, field_typ) = self.load_field(segment_type, field);
                                segment_type = field_typ;
                                self.insert_load_field(load_field);
                            }
                        }
                    }
                    match last {
                        AssignSegment::Field(field) => {
                            let Type::Struct { fields, .. } = segment_type.clone() else {
                                panic!("Cannot store field into type: {segment_type:?}")
                            };
                            let typ = self.expr(expr)?;
                            let (_, expected) = self.load_field(segment_type, field);
                            assert_eq!(typ, expected);
                            if !typ.is_zst() {
                                self.builder.insert(Op::StoreField(fields[**field].0));
                            }
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
                match self.expr(expr)? {
                    Type::Bool => {}
                    other => panic!("Cannot use type: {other:?} in while loop"),
                }
                self.builder.insert(Op::CJump(end_label));
                self.gen_block(&body.stmts)?;
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

                let iter = self.expr(iter)?;
                let ident_typ = match &iter {
                    Type::Range | Type::RangeInclusive => Type::Int,
                    _ => panic!(),
                };

                self.builder.insert_label(start_label);
                let iter_op = match iter {
                    Type::Range => Op::IterRange,
                    Type::RangeInclusive => Op::IterRangeInclusive,
                    typ => panic!("{typ:?}"),
                };
                self.builder.insert(iter_op);
                self.builder.insert(Op::CJump(end_label));

                self.store_new(ident, ident_typ, false, 0..0)?;

                for stmt in &body.stmts {
                    self.r#gen(stmt)?;
                }

                self.builder.insert(Op::Jump(start_label));
                self.builder.insert_label(end_label);

                self.continue_label = prev_continue;
                self.break_label = prev_break;
            }
            Stmt::IfChain(IfChain { first, else_ifs, r#else }) => {
                let typ = self.expr(&first.condition)?;
                match typ {
                    Type::Bool => {}
                    other => panic!("Cannot use type {other:?} in if stmts"),
                }
                let not_lone_if = !else_ifs.is_empty() || r#else.is_some();

                let final_end_label = if not_lone_if { self.builder.create_label() } else { 0 };
                let mut next_label = self.builder.create_label();
                self.builder.insert(Op::CJump(next_label));
                self.gen_block(&first.body.stmts)?;
                if not_lone_if {
                    self.builder.insert(Op::Jump(final_end_label));
                }
                for elseif in else_ifs {
                    self.builder.insert_label(next_label);
                    let typ = self.expr(&elseif.condition)?;
                    match typ {
                        Type::Bool => {}
                        other => panic!("Cannot use type {other:?} in if stmts"),
                    }
                    next_label = self.builder.create_label();
                    self.builder.insert(Op::CJump(next_label));
                    self.gen_block(&elseif.body.stmts)?;
                    if not_lone_if {
                        self.builder.insert(Op::Jump(final_end_label));
                    }
                }
                self.builder.insert_label(next_label);
                if let Some(block) = r#else {
                    self.gen_block(&block.stmts)?;
                }
                if not_lone_if {
                    self.builder.insert_label(final_end_label);
                }
            }
            Stmt::Expr(expr) => {
                let typ = self.expr(expr)?;
                if !typ.is_zst() {
                    self.builder.insert(Op::Pop);
                }
            }
            Stmt::Continue => self.builder.insert(Op::Jump(self.continue_label.unwrap())),
            Stmt::Break => self.builder.insert(Op::Jump(self.break_label.unwrap())),
            Stmt::Return(expr) => {
                let typ = if let Some(expr) = &expr.0 { self.expr(expr)? } else { Type::Null };
                let scope = self.scopes.last().unwrap();
                assert!(
                    scope.ret == typ,
                    "Tried to return {typ:?} from function returning: {:?}",
                    scope.ret
                );
                self.builder.insert(Op::Ret);
            }
            Stmt::Block(block) => {
                for stmt in &block.stmts {
                    self.r#gen(stmt)?;
                }
            }
        }
        Ok(())
    }

    fn var_decl(&mut self, var_decl: &Spanned<VarDecl>, is_const: bool) -> Result<()> {
        let VarDecl { pat, typ, expr } = &**var_decl;
        let expected = typ.as_ref().map(|typ| {
            self.load_explicit_type(typ).unwrap_or_else(|| panic!("Unknown type: {typ:?}"))
        });
        let mut typ = match expr {
            Some(expr) => self.expr(expr)?,
            None => 'block: {
                let expected = expected.clone().unwrap();
                let op = match expected {
                    Type::Null => break 'block Type::Null,
                    Type::Int => Op::LoadIntSmall(0),
                    Type::Str => Op::LoadString { ptr: 0, len: 0 },
                    _ => todo!("{expected:?}"),
                };
                self.builder.insert(op);
                expected
            }
        };
        if let Some(expected) = &expected {
            typ = typ.try_combine(expected).unwrap_or_else(|| panic!("{typ:?} - {expected:?}"));
        }
        self.store_pat(pat, typ, is_const)?;
        Ok(())
    }

    fn store_pat(&mut self, pat: &Spanned<Pat>, typ: Type, is_const: bool) -> Result<()> {
        match &**pat {
            Pat::Array(sections) => {
                let Type::Tuple(exprs) = typ else { panic!("{typ:?}") };
                assert_eq!(exprs.len(), sections.len());
                self.builder.insert(Op::ArrayConcatStack);
                for (pat, typ) in sections.iter().rev().zip(exprs.iter().rev()) {
                    self.store_pat(pat, typ.clone(), is_const)?;
                }
                Ok(())
            }
            Pat::Ident(ident) => self.store_new(ident, typ, is_const, pat.span.clone()),
        }
    }

    fn store(&mut self, ident: &'static str) {
        match self.scopes.last().unwrap().variables.get(ident) {
            Some(var) => {
                assert!(!var.is_const);
                if !var.typ.is_zst() {
                    self.builder.insert(Op::Store(var.offset));
                }
            }
            None => panic!(),
        };
    }

    #[must_use]
    fn load_var_type(&self, ident: &'static str) -> &Type {
        match self.scopes.last().unwrap().variables.get(ident) {
            Some(var) => &var.typ,
            None => &self.scopes.first().unwrap().variables.get(ident).unwrap().typ,
        }
    }

    #[must_use]
    fn load_name_type(&self, type_name: &'static str) -> Option<Type> {
        match self.scopes.last().unwrap().named_types.get(type_name) {
            Some(typ) => Some(typ.clone()),
            None => self.scopes.first().unwrap().named_types.get(type_name).cloned(),
        }
    }

    #[must_use]
    fn load_explicit_type(&self, explicit_typ: &Spanned<ExplicitType>) -> Option<Type> {
        if *explicit_typ.ident == "_" {
            assert!(explicit_typ.generics.is_empty());
            return Some(Type::Unknown);
        }
        let typ = self.load_name_type(*explicit_typ.ident)?;
        Some(match typ {
            Type::Array(typ) if *typ == Type::Unknown => {
                assert_eq!(explicit_typ.generics.len(), 1);
                let generic = self.load_explicit_type(&explicit_typ.generics[0])?;
                if generic.is_zst() {
                    panic!("arrays may not contains ZSTs");
                }
                Type::Array(Rc::new(generic))
            }
            Type::Map { key, value } if *key == Type::Unknown || *value == Type::Unknown => {
                assert_eq!(explicit_typ.generics.len(), 2);
                let generic_key = self.load_explicit_type(&explicit_typ.generics[0])?;
                let generic_value = self.load_explicit_type(&explicit_typ.generics[1])?;
                if generic_key.is_zst() || generic_value.is_zst() {
                    panic!("maps may not contains ZSTs");
                }
                Type::Map {
                    key: Rc::new(self.load_explicit_type(&explicit_typ.generics[0])?),
                    value: Rc::new(self.load_explicit_type(&explicit_typ.generics[1])?),
                }
            }
            Type::Tuple(_) => Type::Tuple(
                explicit_typ
                    .generics
                    .iter()
                    .map(|generic| self.load_explicit_type(generic))
                    .collect::<Option<_>>()?,
            ),
            other => {
                assert_eq!(explicit_typ.generics.len(), 0, "{other:?}");
                other
            }
        })
    }

    fn load(&mut self, ident: Spanned<Ident>) -> Result<Type> {
        Ok(match self.scopes.last().unwrap().variables.get(*ident) {
            Some(var) => {
                match &var.typ {
                    Type::Enum { .. } => {}
                    typ if typ.is_zst() => {}
                    _ => self.builder.insert(Op::Load(var.offset)),
                }
                var.typ.clone()
            }
            None => {
                let scope = self.scopes.first().unwrap();
                let var = scope
                    .variables
                    .get(*ident)
                    .ok_or_else(|| errors::unknown_ident(self.src, ident))?;
                match &var.typ {
                    Type::Enum { .. } => {}
                    typ if typ.is_zst() => {}
                    _ => self.builder.insert(Op::LoadGlobal(var.offset)),
                }
                var.typ.clone()
            }
        })
    }

    fn expr(&mut self, expr: &Expr) -> Result<Type> {
        Ok(match expr {
            Expr::Literal(literal) => 'block: {
                let span = literal.span.clone();
                match &**literal {
                    Literal::Tuple(tuple) => {
                        self.builder.insert(Op::CreateArray);
                        let mut arg_types = vec![];
                        for expr in tuple {
                            arg_types.push(self.expr(expr)?);
                            self.builder.insert(Op::ArrayPush);
                        }
                        Type::Tuple(arg_types.into())
                    }
                    Literal::Map(map) => {
                        self.builder.insert(Op::CreateMap);
                        if map.is_empty() {
                            break 'block Type::Map {
                                key: Rc::new(Type::Unknown),
                                value: Rc::new(Type::Unknown),
                            };
                        }
                        let mut entries = map.iter();
                        let [key, val] = entries.next().unwrap();
                        let key_typ = self.expr(key)?;
                        let val_typ = self.expr(val)?;
                        self.builder.insert(Op::InsertMap);

                        for [key, val] in entries {
                            assert_eq!(self.expr(key)?, key_typ);
                            assert_eq!(self.expr(val)?, val_typ);
                            self.builder.insert(Op::InsertMap);
                        }

                        Type::Map { key: Rc::new(key_typ), value: Rc::new(val_typ) }
                    }
                    Literal::Bool(bool) => {
                        self.builder.insert(Op::LoadBool(*bool));
                        Type::Bool
                    }
                    Literal::Char(char) => {
                        self.builder.insert(Op::LoadChar(*char));
                        Type::Char
                    }
                    Literal::Int(int) => {
                        let op = match (*int).try_into() {
                            Ok(small) => Op::LoadIntSmall(small),
                            Err(_) => Op::LoadInt(*int),
                        };
                        self.builder.insert(op);
                        Type::Int
                    }
                    Literal::String(string) => {
                        let [ptr, len] = self.builder.insert_string(string);
                        self.builder.insert(Op::LoadString { ptr, len });
                        Type::Str
                    }
                    Literal::FString(fstring) => {
                        let mut num_segments = fstring.segments.len() as u16;
                        for (str, expr) in &fstring.segments {
                            let [ptr, len] = self.builder.insert_string(str);
                            if len != 0 {
                                self.builder.insert(Op::LoadString { ptr, len });
                                num_segments += 1;
                            }
                            let typ = self.expr(expr)?;

                            if typ == Type::Null {
                                let [ptr, len] = self.builder.insert_string("null");
                                self.builder.insert(Op::LoadString { ptr, len });
                            } else if typ.is_zst() {
                                todo!()
                            }
                        }
                        let [ptr, len] = self.builder.insert_string(fstring.remaining);
                        if len != 0 {
                            self.builder.insert(Op::LoadString { ptr, len });
                            num_segments += 1;
                        }
                        self.builder.insert(Op::BuildFstr { num_segments });
                        Type::Str
                    }
                    Literal::Ident(ident) => self.load(Spanned { inner: ident, span })?,
                }
            }
            Expr::Binary { op, exprs } => 'block: {
                match op {
                    BinOp::And => {
                        let end_label = self.builder.create_label();
                        let lhs = self.expr(&exprs[0])?;
                        assert_eq!(lhs, Type::Bool, "Cannot use or operator on type {lhs:?}");
                        self.builder.insert(Op::Dup);
                        self.builder.insert(Op::CJump(end_label));
                        self.builder.insert(Op::Pop);
                        let rhs = self.expr(&exprs[1])?;
                        assert_eq!(rhs, Type::Bool, "Cannot use or operator on type {rhs:?}");
                        self.builder.insert_label(end_label);
                        break 'block Type::Bool;
                    }
                    BinOp::Or => {
                        let end_label = self.builder.create_label();
                        let lhs = self.expr(&exprs[0])?;
                        assert_eq!(lhs, Type::Bool, "Cannot use or operator on type {lhs:?}");
                        self.builder.insert(Op::Dup);
                        self.builder.insert(Op::Not);
                        self.builder.insert(Op::CJump(end_label));
                        self.builder.insert(Op::Pop);
                        let rhs = self.expr(&exprs[1])?;
                        assert_eq!(rhs, Type::Bool, "Cannot use or operator on type {rhs:?}");
                        self.builder.insert_label(end_label);
                        break 'block Type::Bool;
                    }
                    _ => {}
                };
                let lhs = self.expr(&exprs[0])?;
                let rhs = self.expr(&exprs[1])?;

                let op = match op {
                    BinOp::Range => Op::Range,
                    BinOp::RangeInclusive => Op::RangeInclusive,
                    BinOp::Mod => Op::Mod,
                    BinOp::Add => {
                        assert_eq!(lhs, Type::Int);
                        assert_eq!(rhs, Type::Int);
                        self.builder.insert(Op::AddInt);
                        break 'block Type::Int;
                    }
                    BinOp::Eq => {
                        assert!(self.can_cmp(&lhs, &rhs), "{lhs:?} - {rhs:?}");
                        self.builder.insert(Op::Eq);
                        break 'block Type::Bool;
                    }
                    BinOp::Greater => {
                        assert!(self.can_cmp(&lhs, &rhs), "{lhs:?} - {rhs:?}");
                        self.builder.insert(Op::Greater);
                        break 'block Type::Bool;
                    }
                    BinOp::Less => {
                        assert!(self.can_cmp(&lhs, &rhs), "{lhs:?} - {rhs:?}");
                        self.builder.insert(Op::Less);
                        break 'block Type::Bool;
                    }
                    BinOp::Neq => {
                        assert!(self.can_cmp(&lhs, &rhs), "{lhs:?} - {rhs:?}");
                        self.builder.insert(Op::Eq);
                        self.builder.insert(Op::Not);
                        break 'block Type::Bool;
                    }
                    _ => todo!("{op:?}"),
                };
                let typ = match (lhs, rhs, op) {
                    (Type::Int, Type::Int, Op::Range) => Type::Range,
                    (Type::Int, Type::Int, Op::RangeInclusive) => Type::RangeInclusive,
                    (_, _, Op::Range | Op::RangeInclusive) => panic!(),
                    // FIXME: This catchall might have false positives
                    (lhs, rhs, _) if lhs == rhs => lhs,
                    (lhs, rhs, op) => panic!("{op:?}: {lhs:?} - {rhs:?}"),
                };
                self.builder.insert(op);
                typ
            }
            Expr::FnCall { function, args } => {
                let mut arg_types = vec![];
                for arg in args {
                    arg_types.push(self.expr(arg)?);
                }
                let typ = self.expr(function)?;
                let ret_type = match typ {
                    Type::Function(fn_type) => {
                        assert_eq!(fn_type.args.len(), arg_types.len(), "{function:?}");
                        for (arg_ty, param_ty) in arg_types.iter().zip(&fn_type.args) {
                            assert_eq!(arg_ty, param_ty);
                        }
                        fn_type.ret.clone()
                    }
                    other => panic!("Cannot call {other:?}"),
                };
                self.builder.insert(Op::FnCall);
                ret_type
            }
            Expr::MethodCall { expr, method, args } => self.method_call(expr, method, args)?,
            Expr::FieldAccess { expr, field } => {
                let typ = self.expr(expr)?;
                let (load_field, field_typ) = self.load_field(typ, field);
                self.insert_load_field(load_field);
                field_typ
            }
            Expr::Index { expr, index } => {
                let container_typ = self.expr(expr)?;
                let index_typ = self.expr(index)?;
                self.builder.insert(Op::Index);
                self.index_type(container_typ, index_typ)
            }
            Expr::InitStruct { ident, fields } => {
                let struct_type = self.load_name_type(ident).unwrap();
                let Type::Struct { name: _, fields: type_fields } = &struct_type else { panic!() };
                // TODO: Reduce struct size for zst fields.
                self.builder.insert(Op::CreateStruct { size: type_fields.len() as u32 });
                for StructInitField { ident, expr } in fields {
                    assert!(type_fields.contains_key(**ident));
                    let typ = match expr {
                        Some(expr) => self.expr(expr)?,
                        None => self.load(ident.clone())?,
                    };
                    assert_eq!(type_fields.get(**ident).unwrap().1, typ);
                    if !typ.is_zst() {
                        self.builder.insert(Op::StoreField(type_fields[**ident].0));
                    }
                }
                struct_type
            }
            Expr::Array(array) => 'block: {
                self.builder.insert(Op::CreateArray);

                if array.is_empty() {
                    break 'block Type::Array(Rc::new(Type::Unknown));
                }
                let mut array_iter = array.iter();
                let typ = self.expr(array_iter.next().unwrap())?;
                if typ.is_zst() {
                    panic!("ZSTs are not supported in arrays");
                }
                self.builder.insert(Op::ArrayPush);
                for expr in array_iter {
                    let next_typ = self.expr(expr)?;
                    assert_eq!(next_typ, typ);
                    self.builder.insert(Op::ArrayPush);
                }
                Type::Array(Rc::new(typ))
            }
            Expr::Unary { op, expr } => {
                let typ = self.expr(expr)?;
                if *op == UnaryOp::Not && typ != Type::Bool {
                    panic!("Cannot use ! operator on {typ:?}");
                }
                if *op == UnaryOp::Neg && typ != Type::Int {
                    panic!("Cannot use - operator on {typ:?}");
                }
                match op {
                    UnaryOp::Not => self.builder.insert(Op::Not),
                    UnaryOp::Neg => self.builder.insert(Op::Neg),
                }
                typ
            }
        })
    }

    fn method_call(&mut self, expr: &Expr, method: &'static str, args: &[Expr]) -> Result<Type> {
        let typ = self.expr(expr)?;
        let (op, method) = self.load_method(typ, method);
        assert_eq!(args.len(), method.args.len(), "{method:?}");
        for (arg, param_typ) in args.iter().zip(method.args) {
            let arg_typ = self.expr(arg)?;
            assert_eq!(param_typ, arg_typ);
        }
        match op {
            LoadMethod::Builtin(builtin) => self.builder.insert(Op::CallBuiltinMethod(builtin)),
        }
        Ok(method.ret)
    }

    fn can_cmp(&self, lhs: &Type, rhs: &Type) -> bool {
        match (lhs, rhs) {
            (Type::Int, Type::Int) => true,
            (Type::Char, Type::Char) => true,
            (Type::Str, Type::Str) => true,
            (Type::Bool, Type::Bool) => true,
            (Type::Tuple(lhs), Type::Tuple(rhs)) => self.can_cmp_tuples(lhs, rhs),
            _ => false,
        }
    }

    fn can_cmp_tuples(&self, lhs: &[Type], rhs: &[Type]) -> bool {
        (lhs.len() == rhs.len()) && lhs.iter().zip(rhs).all(|(lhs, rhs)| self.can_cmp(lhs, rhs))
    }

    fn index_type(&self, container: Type, index: Type) -> Type {
        match container {
            Type::Str => match index {
                Type::Range => Type::Str,
                Type::Int => Type::Char,
                _ => panic!("Cannot index str with type: {index:?}"),
            },
            Type::Array(of) => match index {
                Type::Int => of.clone_inner(),
                _ => panic!("Cannot index Array({of:?}) with type: {index:?}"),
            },
            _ => panic!("Cannot index {container:?}"),
        }
    }

    fn insert_load_field(&mut self, load_field: LoadField) {
        match load_field {
            LoadField::Builtin(builtin) => self.builder.insert(Op::LoadBuiltinField(builtin)),
            LoadField::StructField(field) => self.builder.insert(Op::LoadField(field)),
            LoadField::EnumVariant(variant) => self.builder.insert(Op::LoadVariant(variant)),
            LoadField::ZstField => {}
        }
    }

    fn load_field(&mut self, typ: Type, field: &'static str) -> (LoadField, Type) {
        use BuiltinField::*;

        let (builtin_field, typ) = match typ {
            Type::Enum { fields, id, .. } if fields.contains_key(field) => {
                return (
                    LoadField::EnumVariant(self.builder.insert_identifer(field)),
                    Type::EnumVariant { id },
                );
            }
            Type::Struct { name, fields } => match fields.get(field) {
                Some((_, field_type)) if field_type.is_zst() => {
                    return (LoadField::ZstField, field_type.clone());
                }
                Some((i, field_type)) => return (LoadField::StructField(*i), field_type.clone()),
                None => panic!("struct {name} does not contain field: {field}"),
            },
            Type::Str => match field {
                "len" => (StrLen, Type::Int),
                _ => panic!("type str does not contain field: {field}"),
            },
            Type::Array(of) => match field {
                "len" => (ArrayLen, Type::Int),
                _ => panic!("type Array({of:?}) does not contain field: {field}"),
            },
            _ => panic!("type {typ:?} does not contain field: {field}"),
        };
        (LoadField::Builtin(builtin_field), typ)
    }

    fn load_method(&mut self, typ: Type, method: &'static str) -> (LoadMethod, FnSig) {
        // TODO: Should these function signatures contain self as their first argument?

        use MethodBuiltin::*;

        let (builtin_field, fn_sig) = match typ {
            Type::Enum { .. } => todo!("enum methods"),
            Type::Struct { .. } => todo!("struct methods"),
            Type::Str => match method {
                "trim" => (StrTrim, FnSig { ret: Type::Str, args: [].into() }),
                "starts_with" => {
                    (StrStartsWith, FnSig { ret: Type::Bool, args: [Type::Str].into() })
                }
                "is_digit" => (StrIsDigit, FnSig { ret: Type::Bool, args: [].into() }),
                "is_alphabetic" => (StrIsAlphabetic, FnSig { ret: Type::Bool, args: [].into() }),
                "lines" => {
                    (StrLines, FnSig { ret: Type::Array(Rc::new(Type::Str)), args: [].into() })
                }
                _ => panic!("type str does not contain method: {method}"),
            },
            Type::Char => match method {
                "is_digit" => (CharIsDigit, FnSig { ret: Type::Bool, args: [].into() }),
                "is_alphabetic" => (CharIsAlphabetic, FnSig { ret: Type::Bool, args: [].into() }),
                _ => panic!("type char does not contain method: {method}"),
            },
            Type::Int => match method {
                "abs" => (IntAbs, FnSig { ret: Type::Int, args: [].into() }),
                _ => panic!("type int does not contain method: `{method}`"),
            },
            Type::Map { key, value } => match method {
                "insert" => (MapInsert, FnSig {
                    ret: Type::Null,
                    args: [(*key).clone(), (*value).clone()].into(),
                }),
                "remove" => {
                    (MapRemove, FnSig { ret: Type::Null, args: [key.clone_inner()].into() })
                }
                "get" => {
                    (MapGet, FnSig { ret: value.clone_inner(), args: [key.clone_inner()].into() })
                }
                _ => panic!("type map does not contain method: {method}"),
            },
            Type::Array(of) => match method {
                "sort" if *of == Type::Int => {
                    (ArraySortInt, FnSig { ret: Type::Array(of), args: [].into() })
                }
                "pop" => (ArrayPop, FnSig { ret: of.clone_inner(), args: [].into() }),
                "push" => (ArrayPush, FnSig { ret: Type::Null, args: [of.clone_inner()].into() }),
                _ => panic!("type Array({of:?}) does not contain method: {method}"),
            },
            _ => panic!("type {typ:?} does not contain method: {method}"),
        };
        (LoadMethod::Builtin(builtin_field), fn_sig)
    }

    fn finish(self) -> Vec<u8> {
        self.builder.finish()
    }
}
