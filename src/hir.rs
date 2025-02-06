#![expect(dead_code)]

use std::{
    collections::{BTreeMap, HashMap},
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use miette::Result;
use rustc_hash::FxHashMap;

use crate::{
    builtints::Builtin,
    parser::{
        self as ast, AssignSegment, BinOp, ExplicitType, Pat, Spanned, Stmt, StructInitField,
        UnaryOp, VarDecl,
    },
    typck::{Substitutions, Ty, TyCon, TyKind, TyVar, unify},
};

#[derive(Debug)]
pub enum Item {
    Function(Function),
    Loop(Block),
    ForLoop(ForLoop),
    IfChain(IfChain),
    Expr(Expr),
    Block(Block),
    Assign(Assign),
    Continue,
    Break,
    Return(Return),
}

#[derive(Debug)]
pub struct Function {
    pub name: &'static str,
    pub ident: Ident,
    pub params: Vec<Ident>,
    pub stack_size: usize,
    pub ty: Ty,
    pub ret: TyVar,
    pub body: Block,
}

#[derive(Debug)]
pub struct Block {
    pub items: Vec<Item>,
}

impl Block {
    const EMPTY: Self = Self { items: vec![] };
}

#[derive(Debug)]
pub struct ForLoop {
    pub ident: Option<Ident>,
    pub iter: Expr,
    pub body: Block,
}

#[derive(Debug)]
pub struct IfChain {
    pub chain: Vec<(Expr, Block)>,
    pub end: Block,
}

#[derive(Debug)]
pub struct Assign {
    pub root: Ident,
    pub expr: Expr,
}

#[derive(Debug)]
pub struct Return {
    expr: Option<Expr>,
}

#[derive(Debug)]
pub struct Expr {
    pub ty: Ty,
    pub kind: ExprKind,
}

#[derive(Debug)]
pub enum ExprKind {
    Unary { expr: Box<Expr>, op: UnaryOp },
    Binary { exprs: Box<[Expr; 2]>, op: BinOp },
    FnCall { expr: Box<Expr>, args: Vec<Expr> },
    FieldAccess { expr: Box<Expr>, field: &'static str },
    MethodCall { expr: Box<Expr>, method: &'static str, args: Vec<Expr> },
    Index { expr: Box<Expr>, index: Box<Expr> },
    StructInit { ident: &'static str, fields: Vec<(&'static str, Expr)> },
    Array(Vec<Expr>),
    Tuple(Vec<Expr>),
    Map(Vec<[Expr; 2]>),
    Ident(Ident),
    Bool(bool),
    Char(char),
    Int(i64),
    Str(&'static str),
    Fstr(Fstr),
}

#[derive(Debug, Clone)]
pub struct Ident {
    pub ty: Ty,
    pub offset: Offset,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Offset {
    Local(u32),
    Global(u32),
}

#[derive(Debug)]
pub struct Fstr {
    pub segments: Vec<(&'static str, Expr)>,
    pub remaining: &'static str,
}

pub struct Lowering<'src> {
    pub named_types: FxHashMap<&'static str, Ty>,
    pub structs: FxHashMap<&'static str, Rc<BTreeMap<&'static str, Ty>>>,
    pub subs: Substitutions,
    scopes: Vec<FnScope>,
    src: &'src str,
}

#[derive(Debug)]
pub struct FnScope {
    ret_var: TyVar,
    variables: FxHashMap<&'static str, Ident>,
}

impl<'src> Lowering<'src> {
    pub fn new(src: &'src str) -> Self {
        let mut subs = Substitutions::new();
        let ret_var = TyVar::uniq();
        unify(&Ty::Var(ret_var), &Ty::null(), &mut subs);

        let mut named_types = FxHashMap::default();

        let generics = Rc::new([]);
        let builtin_names = ["int", "char", "bool", "str", "null", "array", "map", "tuple"];
        for name in builtin_names {
            named_types.insert(
                name,
                Ty::Con(TyCon { kind: TyKind::Named(name), generics: generics.clone() }),
            );
        }

        let mut scope = FnScope { ret_var, variables: FxHashMap::default() };

        for builtin in Builtin::ALL {
            let name = builtin.name();
            let ty = match builtin {
                Builtin::Println => Ty::func([Ty::str()], Ty::null()),
                Builtin::Assert => Ty::func([Ty::bool()], Ty::bool()),
                Builtin::Exit => Ty::func([Ty::int()], Ty::null()),
                Builtin::ParseInt => Ty::func([Ty::str()], Ty::int()),
                Builtin::ReadFile => Ty::func([Ty::str()], Ty::str()),
            };
            scope.insert(name, ty, true);
        }

        scope.insert("null", Ty::null(), true);

        Self { src, subs, scopes: vec![scope], named_types, structs: HashMap::default() }
    }
}

impl FnScope {
    /// Returns none if name is ignored ("_")
    fn insert(&mut self, name: &'static str, ty: Ty, is_global: bool) -> Option<Ident> {
        if name == "_" {
            return None;
        }
        let offset = self.variables.len() as u32;
        let offset = if is_global { Offset::Global(offset) } else { Offset::Local(offset) };
        let ident = Ident { ty, offset };
        let prev = self.variables.insert(name, ident.clone());
        assert!(prev.is_none(), "{name}: {ident:?}");
        Some(ident)
    }
}

impl Lowering<'_> {
    /// Returns none if name is ignored  ("_")
    pub fn insert_scope(&mut self, name: &'static str, ty: Ty) -> Option<Ident> {
        if self.scopes.len() == 1 {
            self.scope().insert(name, ty, true)
        } else {
            self.scope().insert(name, ty, false)
        }
    }
}

impl Lowering<'_> {
    pub fn block(&mut self, block: &[Spanned<Stmt>]) -> Result<Block> {
        let mut items = vec![];
        for stmt in block {
            self.stmt(stmt, &mut items)?;
        }
        Ok(Block { items })
    }

    fn stmt(&mut self, stmt: &Stmt, out: &mut Vec<Item>) -> Result<()> {
        match stmt {
            Stmt::WhileLoop(while_loop) => self.while_loop(while_loop, out)?,
            Stmt::ForLoop(for_loop) => self.for_loop(for_loop, out)?,
            Stmt::IfChain(if_chain) => self.if_chain(if_chain, out)?,
            Stmt::Let(var_decl) => self.var_decl(var_decl, false, out)?,
            Stmt::Const(var_decl) => self.var_decl(var_decl, true, out)?,
            Stmt::Assign(assign) => self.assign(assign, out)?,
            Stmt::Struct(struct_) => self.struct_(struct_, out)?,
            Stmt::Enum(enum_) => self.enum_(enum_, out)?,
            Stmt::Function(func) => self.function(func, out)?,
            Stmt::Return(ret) => self.ret(ret, out)?,
            Stmt::Continue => out.push(Item::Continue),
            Stmt::Break => out.push(Item::Break),
            Stmt::Expr(expr) => out.push(Item::Expr(self.expr(expr)?)),
            _ => todo!("{stmt:?}"),
        }
        Ok(())
    }

    fn while_loop(&mut self, while_loop: &ast::WhileLoop, out: &mut Vec<Item>) -> Result<()> {
        let branch_expr = self.expr(&while_loop.expr)?;
        let exit_condition = Item::IfChain(IfChain {
            chain: vec![(branch_expr, Block { items: vec![Item::Break] })],
            end: Block::EMPTY,
        });
        let mut new_body = vec![exit_condition];
        new_body.append(&mut self.block(&while_loop.body.stmts)?.items);
        out.push(Item::Loop(Block { items: new_body }));
        Ok(())
    }

    fn for_loop(&mut self, for_loop: &ast::ForLoop, out: &mut Vec<Item>) -> Result<()> {
        let iter = self.expr(&for_loop.iter)?;
        // TODO: Don't fully substitute this type.
        let Ty::Con(iter_typ) = iter.ty.sub(&self.subs) else { panic!() };
        let item_ty = self.iter_item_ty(&iter_typ);

        let iter_ident = self.insert_scope(&for_loop.ident, item_ty);
        let body = self.block(&for_loop.body.stmts)?;

        // TODO: Handle for loop sugar here instead of later.
        out.push(Item::ForLoop(ForLoop { ident: iter_ident, iter, body }));
        Ok(())
    }

    fn if_chain(&mut self, if_chain: &ast::IfChain, out: &mut Vec<Item>) -> Result<()> {
        let mut chain = vec![];

        for if_stmt in [&if_chain.first].into_iter().chain(&if_chain.r#else_ifs) {
            let condition = self.expr(&if_stmt.condition)?;
            unify(&condition.ty, &Ty::bool(), &mut self.subs);
            let block = self.block(&if_stmt.body.stmts)?;
            chain.push((condition, block));
        }

        let end = if let Some(r#else) = &if_chain.r#else {
            self.block(&r#else.stmts)?
        } else {
            Block::EMPTY
        };

        out.push(Item::IfChain(IfChain { chain, end }));
        Ok(())
    }

    fn iter_item_ty(&mut self, iter: &TyCon) -> Ty {
        // FIXME: .............
        match iter.kind {
            TyKind::Named("range") => Ty::int(),
            TyKind::Named("range_inclusive") => Ty::int(),
            _ => panic!("{iter:?}"),
        }
    }

    fn var_decl(
        &mut self,
        var_decl: &Spanned<VarDecl>,
        is_const: bool,
        out: &mut Vec<Item>,
    ) -> Result<()> {
        let _ = is_const;
        let Pat::Ident(ident) = &*var_decl.pat else { todo!() };
        assert!(!self.scope().variables.contains_key(ident), "{ident:?} - {:?}", self.scope());

        let mut ty = None;
        if let Some(expl_ty) = &var_decl.typ {
            ty = Some(self.load_explicit_type(expl_ty)?);
        }
        let ty = ty.unwrap_or_else(|| Ty::Var(TyVar::uniq()));

        let expr = self.expr(var_decl.expr.as_ref().unwrap())?;
        unify(&expr.ty, &ty, &mut self.subs);
        let ident = self.insert_scope(ident, ty).unwrap();
        out.push(Item::Assign(Assign { root: ident, expr }));
        Ok(())
    }

    fn assign(&mut self, assign: &ast::Assign, out: &mut Vec<Item>) -> Result<()> {
        let mut var = self.load_var(&assign.root).unwrap().ty;
        for segment in &assign.segments {
            match segment {
                AssignSegment::Index(_) => panic!(),
                AssignSegment::Field(field) => {
                    var = self.field_ty(&var, field);
                }
            }
        }
        let expr = self.expr(&assign.expr)?;
        unify(&var, &expr.ty, &mut self.subs);

        let root = self.load_var(&assign.root).unwrap();
        // TODO: Assignment should pass all segments
        out.push(Item::Assign(Assign { root, expr }));
        Ok(())
    }

    fn struct_(&mut self, struct_: &ast::Struct, out: &mut Vec<Item>) -> Result<()> {
        let mut fields = BTreeMap::new();
        for (field, expl_ty) in &struct_.fields {
            let ty = self.load_explicit_type(expl_ty)?;
            fields.insert(**field, ty);
        }
        let fields = Rc::new(fields);
        let ty = Ty::Con(TyCon {
            kind: TyKind::Struct { name: &struct_.ident, fields },
            generics: Rc::new([]),
        });
        let prev = self.named_types.insert(&struct_.ident, ty);
        assert!(prev.is_none());
        _ = out;
        Ok(())
    }

    fn enum_(&mut self, enum_: &ast::Enum, out: &mut Vec<Item>) -> Result<()> {
        static ENUM_ID: AtomicU32 = AtomicU32::new(0);
        let enum_id = ENUM_ID.fetch_add(1, Ordering::Relaxed);

        let mut variants = BTreeMap::<&str, _>::new();
        for (offset, field) in enum_.variants.iter().enumerate() {
            variants.insert(field, offset as u32);
        }
        let variants = Rc::new(variants);
        let ty = Ty::Con(TyCon {
            kind: TyKind::Enum { id: enum_id, name: &enum_.ident, variants },
            generics: Rc::new([]),
        });
        let _ = self.insert_scope(&enum_.ident, ty.clone());

        let prev = self
            .named_types
            .insert(&enum_.ident, Ty::Con(TyCon::from(TyKind::Variant { id: enum_id })));
        assert!(prev.is_none());
        _ = out;
        Ok(())
    }

    fn function(&mut self, func: &ast::Function, out: &mut Vec<Item>) -> Result<()> {
        let fn_var = TyVar::uniq();
        let ident = self.insert_scope(&func.ident, Ty::Var(fn_var)).unwrap();

        let ret_var = TyVar::uniq();
        self.scopes.push(FnScope { ret_var, variables: FxHashMap::default() });
        let mut params = vec![];
        for (ident, expl_typ) in &func.params {
            let ty = self.load_explicit_type(expl_typ)?;
            let var = TyVar::uniq();
            unify(&Ty::Var(var), &ty, &mut self.subs);
            let ident = self.insert_scope(ident, Ty::Var(var)).unwrap();
            params.push(ident);
        }
        let fn_params = params.clone();

        if let Some(ret_ty) = &func.ret_type {
            let ret_ty = self.load_explicit_type(ret_ty)?;
            unify(&Ty::Var(ret_var), &ret_ty, &mut self.subs);
        } else {
            unify(&Ty::Var(ret_var), &Ty::null(), &mut self.subs);
        }

        let body = self.block(&func.body.stmts)?;
        let last_scope = self.scopes.pop().unwrap();
        let stack_size = last_scope.variables.len();

        let fn_ty = Ty::Con(TyCon::from(TyKind::Function {
            params: params.iter().map(|ident| ident.ty.clone()).collect(),
            ret: Rc::new(Ty::Var(ret_var)),
        }));
        unify(&Ty::Var(fn_var), &fn_ty, &mut self.subs);

        out.push(Item::Function(Function {
            name: &func.ident,
            ident,
            ty: fn_ty,
            stack_size,
            params: fn_params,
            ret: ret_var,
            body,
        }));
        Ok(())
    }

    fn ret(&mut self, ret: &ast::Return, out: &mut Vec<Item>) -> Result<()> {
        let ret_var = self.scope().ret_var;

        let expr = if let Some(expr) = &ret.0 {
            let expr = self.expr(expr)?;
            unify(&expr.ty, &Ty::Var(ret_var), &mut self.subs);
            Some(expr)
        } else {
            unify(&Ty::null(), &Ty::Var(ret_var), &mut self.subs);
            None
        };

        out.push(Item::Return(Return { expr }));
        Ok(())
    }

    fn load_explicit_type(&self, expl_ty: &Spanned<ExplicitType>) -> Result<Ty> {
        if expl_ty.is_inferred() {
            return Ok(Ty::Var(TyVar::uniq()));
        }
        let ty = self
            .named_types
            .get(&**expl_ty.ident)
            .unwrap_or_else(|| panic!("{:?}", expl_ty))
            .clone();
        let Ty::Con(tycon) = ty else { panic!() };
        Ok(Ty::Con(TyCon {
            kind: tycon.kind,
            generics: expl_ty
                .generics
                .iter()
                .map(|g| self.load_explicit_type(g))
                .collect::<Result<_>>()?,
        }))
    }

    fn expr(&mut self, expr: &ast::Expr) -> Result<Expr> {
        match expr {
            ast::Expr::Literal(literal) => self.literal(literal),
            ast::Expr::Unary { op, expr } => self.unary(*op, expr),
            ast::Expr::Binary { op, exprs } => self.binary(*op, &exprs[0], &exprs[1]),
            ast::Expr::Array(exprs) => self.array(exprs),
            ast::Expr::FnCall { function, args } => self.fn_call(function, args),
            ast::Expr::FieldAccess { expr, field } => self.field_access(expr, field),
            ast::Expr::MethodCall { expr, method, args } => self.method_call(expr, method, args),
            ast::Expr::Index { expr, index } => self.index(expr, index),
            ast::Expr::InitStruct { ident, fields } => self.init_struct(ident, fields),
        }
    }

    fn literal(&mut self, literal: &ast::Literal) -> Result<Expr> {
        Ok(match literal {
            ast::Literal::Bool(bool) => Expr { ty: Ty::bool(), kind: ExprKind::Bool(*bool) },
            ast::Literal::Int(int) => Expr { ty: Ty::int(), kind: ExprKind::Int(*int) },
            ast::Literal::Char(char) => Expr { ty: Ty::char(), kind: ExprKind::Char(*char) },
            ast::Literal::String(str) => Expr { ty: Ty::str(), kind: ExprKind::Str(str) },
            ast::Literal::FString(fstring) => self.fstr(fstring)?,
            ast::Literal::Ident(ident) => {
                let ident = self.load_var(ident).expect(ident);
                Expr { ty: ident.ty.clone(), kind: ExprKind::Ident(ident) }
            }
            ast::Literal::Map(map) => self.map(map)?,
            ast::Literal::Tuple(tuple) => self.tuple(tuple)?,
        })
    }

    fn fstr(&mut self, fstring: &ast::FString) -> Result<Expr> {
        let mut segments = vec![];
        for (str, aexpr) in &fstring.segments {
            segments.push((*str, self.expr(aexpr)?));
        }
        let remaining = fstring.remaining;
        Ok(Expr { ty: Ty::str(), kind: ExprKind::Fstr(Fstr { segments, remaining }) })
    }

    fn scope(&mut self) -> &mut FnScope {
        self.scopes.last_mut().unwrap()
    }

    fn load_var(&mut self, name: &'static str) -> Option<Ident> {
        match self.scopes.last().unwrap().variables.get(name) {
            Some(ident) => Some(ident.clone()),
            None => self.scopes.first().unwrap().variables.get(name).cloned(),
        }
    }

    fn unary(&mut self, op: UnaryOp, aexpr: &ast::Expr) -> Result<Expr> {
        let expr = self.expr(aexpr)?;
        Ok(Expr { ty: expr.ty.clone(), kind: ExprKind::Unary { expr: Box::new(expr), op } })
    }

    fn binary(&mut self, op: BinOp, left: &ast::Expr, right: &ast::Expr) -> Result<Expr> {
        let left = self.expr(left)?;
        let right = self.expr(right)?;
        unify(&left.ty, &right.ty, &mut self.subs);
        let ty = self.binary_op_out(op, &left.ty);

        Ok(Expr { ty, kind: ExprKind::Binary { exprs: Box::new([left, right]), op } })
    }

    fn binary_op_out(&mut self, op: BinOp, ty: &Ty) -> Ty {
        match op {
            BinOp::Add | BinOp::Mod => ty.clone(),
            BinOp::Eq | BinOp::Neq | BinOp::Less | BinOp::Greater => Ty::bool(),
            BinOp::Range => {
                unify(ty, &Ty::int(), &mut self.subs);
                Ty::range()
            }
            BinOp::RangeInclusive => {
                unify(ty, &Ty::int(), &mut self.subs);
                Ty::range_inclusive()
            }
            BinOp::And | BinOp::Or => {
                unify(ty, &Ty::bool(), &mut self.subs);
                Ty::bool()
            }
            _ => todo!("{op:?}"),
        }
    }

    fn array(&mut self, aexprs: &[ast::Expr]) -> Result<Expr> {
        let var = TyVar::uniq();
        let ty = Ty::array(var);

        let mut exprs = vec![];
        for aexpr in aexprs {
            let expr = self.expr(aexpr)?;
            unify(&Ty::Var(var), &expr.ty, &mut self.subs);
            exprs.push(expr);
        }
        Ok(Expr { kind: ExprKind::Array(exprs), ty })
    }

    fn tuple(&mut self, aexprs: &[Spanned<ast::Expr>]) -> Result<Expr> {
        let mut generics = Vec::with_capacity(aexprs.len());
        let mut exprs = Vec::with_capacity(aexprs.len());

        for aexpr in aexprs {
            let expr = self.expr(aexpr)?;
            generics.push(expr.ty.clone());
            exprs.push(expr);
        }
        Ok(Expr { kind: ExprKind::Tuple(exprs), ty: Ty::tuple(generics.into()) })
    }

    fn map(&mut self, init: &[[ast::Expr; 2]]) -> Result<Expr> {
        let mut entries = Vec::with_capacity(init.len());
        let key_ty = TyVar::uniq();
        let value_ty = TyVar::uniq();

        for [key, value] in init {
            let key = self.expr(key)?;
            let value = self.expr(value)?;

            unify(&key.ty, &Ty::Var(key_ty), &mut self.subs);
            unify(&value.ty, &Ty::Var(value_ty), &mut self.subs);

            entries.push([key, value]);
        }
        let ty = Ty::map(key_ty, value_ty);
        Ok(Expr { ty, kind: ExprKind::Map(entries) })
    }

    fn fn_call(&mut self, func: &ast::Expr, args: &[Spanned<ast::Expr>]) -> Result<Expr> {
        // FIXME: Not entirely sure how to avoid substituting the type here.

        let expr = self.expr(func)?;
        let fn_ty = expr.ty.sub(&self.subs);
        let Ty::Con(TyCon { kind, .. }) = fn_ty else { panic!() };
        let TyKind::Function { params, ret } = kind else { panic!("{kind:?}") };
        assert_eq!(args.len(), params.len());
        let mut new_args = Vec::with_capacity(args.len());
        for (arg, param) in args.iter().zip(&*params) {
            let arg = self.expr(arg)?;
            unify(&arg.ty, param, &mut self.subs);
            new_args.push(arg);
        }
        Ok(Expr {
            ty: (*ret).clone(),
            kind: ExprKind::FnCall { expr: Box::new(expr), args: new_args },
        })
    }

    fn field_access(&mut self, expr: &ast::Expr, field: &'static str) -> Result<Expr> {
        let expr = self.expr(expr)?;
        let field_ty = self.field_ty(&expr.ty, field);
        Ok(Expr { ty: field_ty, kind: ExprKind::FieldAccess { expr: Box::new(expr), field } })
    }

    fn field_ty(&self, ty: &Ty, field: &'static str) -> Ty {
        let Ty::Con(tycon) = ty.sub(&self.subs) else { panic!() };
        match tycon.kind {
            TyKind::Struct { fields, .. } => fields.get(field).unwrap().clone(),
            TyKind::Enum { variants, id, .. } => {
                assert!(
                    variants.contains_key(field),
                    "type `{ty:?}` does not contain field: {field:?}"
                );
                Ty::Con(TyCon::from(TyKind::Variant { id }))
            }
            TyKind::Named("array") => match field {
                "len" => Ty::int(),
                _ => todo!("{field:?}"),
            },
            TyKind::Named("str") => match field {
                "len" => Ty::int(),
                _ => todo!("{field:?}"),
            },
            _ => todo!("type `{:?}` does not contain field: `{field}`", tycon.kind),
        }
    }

    fn method_call(
        &mut self,
        expr: &ast::Expr,
        method: &'static str,
        args: &[Spanned<ast::Expr>],
    ) -> Result<Expr> {
        let expr = self.expr(expr)?;
        let params = self.method_params(&expr.ty, method);
        assert_eq!(args.len() + 1, params.len());
        let mut new_args = Vec::with_capacity(args.len());
        for (arg, param) in args.iter().zip(&*params) {
            let arg = self.expr(arg)?;
            unify(&arg.ty, param, &mut self.subs);
            new_args.push(arg);
        }
        let ret = params.last().unwrap().clone();
        Ok(Expr {
            ty: ret,
            kind: ExprKind::MethodCall { expr: Box::new(expr), method, args: new_args },
        })
    }

    fn method_params(&mut self, ty: &Ty, method: &'static str) -> Rc<[Ty]> {
        let Ty::Con(tycon) = ty.sub(&self.subs) else { panic!() };
        let name = match tycon.kind {
            TyKind::Named(name) => name,
            _ => panic!(),
        };
        match name {
            "int" => match method {
                "abs" => Rc::new([Ty::int()]),
                _ => todo!("`{method}`"),
            },
            "char" => match method {
                "is_digit" => Rc::new([Ty::bool()]),
                "is_alphabetic" => Rc::new([Ty::bool()]),
                _ => todo!("`{method:?}`"),
            },
            "str" => match method {
                "trim" => Rc::new([Ty::str()]),
                "starts_with" => Rc::new([Ty::str(), Ty::bool()]),
                "is_digit" => Rc::new([Ty::bool()]),
                "is_alphabetic" => Rc::new([Ty::bool()]),
                _ => todo!("`{method}`"),
            },
            "array" => match method {
                "push" => Rc::new([tycon.generics[0].clone(), Ty::null()]),
                "pop" => Rc::new([tycon.generics[0].clone()]),
                "sort" => Rc::new([ty.clone()]),
                _ => todo!("`{method}`"),
            },
            "map" => match method {
                "insert" => {
                    Rc::new([tycon.generics[0].clone(), tycon.generics[1].clone(), Ty::null()])
                }
                "get" => Rc::new([tycon.generics[0].clone(), tycon.generics[1].clone()]),
                "remove" => Rc::new([tycon.generics[0].clone(), Ty::null()]),
                _ => todo!("`{method}`"),
            },

            _ => panic!("type `{:?}` does not contain method `{method}`", tycon),
        }
    }

    fn index(&mut self, expr: &ast::Expr, index: &ast::Expr) -> Result<Expr> {
        let expr = self.expr(expr)?;
        let index = self.expr(index)?;

        let ty = self.index_ty(&expr.ty, &index.ty);
        Ok(Expr { ty, kind: ExprKind::Index { expr: Box::new(expr), index: Box::new(index) } })
    }

    fn index_ty(&mut self, ty: &Ty, index: &Ty) -> Ty {
        let Ty::Con(index) = index.sub(&self.subs) else { panic!() };
        let Ty::Con(ty) = ty.sub(&self.subs) else { panic!() };
        assert!(index.generics.is_empty());
        let TyKind::Named(ty_name) = ty.kind else { panic!() };
        let TyKind::Named(index_name) = index.kind else { panic!() };

        match (ty_name, index_name) {
            ("array", "int") => ty.generics[0].clone(),
            ("array", "range") => Ty::Con(ty),
            ("str", "int") => Ty::char(),
            ("str", "range") => Ty::str(),
            _ => todo!("{ty:?}"),
        }
    }

    fn init_struct(
        &mut self,
        ident: &'static str,
        init_fields: &[StructInitField],
    ) -> Result<Expr> {
        let Ty::Con(tycon) = self.named_types.get(ident).unwrap().clone() else { panic!() };
        let TyKind::Struct { fields, .. } = tycon.kind else { panic!() };
        let mut new_fields = vec![];
        for init in init_fields {
            let ty = fields.get(*init.ident).unwrap();
            let init_expr = match init.expr.as_ref() {
                Some(expr) => {
                    let expr = self.expr(expr)?;
                    unify(ty, &expr.ty, &mut self.subs);
                    expr
                }
                None => Expr {
                    ty: ty.clone(),
                    kind: ExprKind::Ident(self.load_var(&init.ident).unwrap()),
                },
            };
            new_fields.push((*init.ident, init_expr));
        }
        let ty =
            Ty::Con(TyCon { kind: TyKind::Struct { name: ident, fields }, generics: Rc::new([]) });
        Ok(Expr { ty, kind: ExprKind::StructInit { ident, fields: new_fields } })
    }
}

impl Expr {
    fn uniq(kind: ExprKind) -> Self {
        Self { kind, ty: Ty::Var(TyVar::uniq()) }
    }
}

macro_rules! impl_ty_const {
    ($($name: ident),+) => {
        $(pub fn $name() -> Ty {
            thread_local! {
                static CACHE: TyCon = TyCon { kind: TyKind::Named(stringify!($name)), generics: Rc::new([]) };
            }
            CACHE.with(|ty| Ty::Con(ty.clone()))
        })+

    };
}

impl Ty {
    impl_ty_const!(str, int, bool, char, null, range, range_inclusive);

    pub fn array(of: TyVar) -> Ty {
        Ty::Con(TyCon { kind: TyKind::Named("array"), generics: Rc::new([Ty::Var(of)]) })
    }

    pub fn map(key: TyVar, val: TyVar) -> Ty {
        Ty::Con(TyCon {
            kind: TyKind::Named("map"),
            generics: Rc::new([Ty::Var(key), Ty::Var(val)]),
        })
    }

    pub fn func(params: impl IntoIterator<Item = Ty>, ret: Ty) -> Ty {
        Ty::Con(TyCon::from(TyKind::Function {
            params: params.into_iter().collect(),
            ret: Rc::new(ret),
        }))
    }

    pub fn tuple(generics: Rc<[Ty]>) -> Ty {
        Ty::Con(TyCon { kind: TyKind::Named("tuple"), generics })
    }
}
