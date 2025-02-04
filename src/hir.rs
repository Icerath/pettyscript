#![expect(dead_code)]

use std::rc::Rc;

use miette::Result;
use rustc_hash::FxHashMap;

use crate::{
    parser::{self as ast, BinOp, ExplicitType, Pat, Spanned, Stmt, UnaryOp, VarDecl},
    typck::{Substitutions, Ty, TyCon, TyVar, unify},
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
    name: &'static str,
    ident: Ident,
    params: Vec<Ty>,
    ret: TyVar,
    body: Block,
}

#[derive(Debug)]
pub struct Block {
    items: Vec<Item>,
}

impl Block {
    const EMPTY: Self = Self { items: vec![] };
}

#[derive(Debug)]
pub struct ForLoop {
    ident: Option<Ident>,
    iter: Expr,
    body: Block,
}

#[derive(Debug)]
pub struct IfChain {
    chain: Vec<(Expr, Block)>,
    end: Block,
}

#[derive(Debug)]
pub struct Assign {
    ident: &'static str,
    expr: Expr,
}

#[derive(Debug)]
pub struct Return {
    expr: Option<Expr>,
}

#[derive(Debug)]
pub struct Expr {
    ty: Ty,
    kind: ExprKind,
}

#[derive(Debug)]
pub enum ExprKind {
    Unary { expr: Box<Expr>, op: UnaryOp },
    Binary { exprs: Box<[Expr; 2]>, op: BinOp },
    FnCall { expr: Box<Expr>, args: Vec<Expr> },
    FieldAccess { expr: Box<Expr>, field: &'static str },
    MethodCall { expr: Box<Expr>, method: &'static str, args: Vec<Expr> },
    Array(Vec<Expr>),
    Ident(Ident),
    Bool(bool),
    Char(char),
    Int(i64),
    Str(&'static str),
    Fstr(Fstr),
}

#[derive(Debug, Clone, Copy)]
pub struct Ident {
    ty: TyVar,
    local: usize,
}

#[derive(Debug)]
pub struct Fstr {
    pub segments: Vec<(&'static str, Expr)>,
    pub remaining: &'static str,
}

pub struct Lowering<'src> {
    pub named_types: FxHashMap<&'static str, Ty>,
    pub subs: Substitutions,
    scopes: Vec<FnScope>,
    src: &'src str,
}

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
        named_types.insert("int", Ty::int());
        named_types.insert("char", Ty::char());
        named_types.insert("bool", Ty::bool());
        named_types.insert("str", Ty::str());
        named_types.insert("null", Ty::null());
        named_types.insert("array", Ty::array(TyVar::ILLEGAL));

        let mut scope = FnScope { ret_var, variables: FxHashMap::default() };

        let println_var = TyVar::uniq();
        let println = Ty::func([Ty::str()], Ty::null());
        unify(&Ty::Var(println_var), &println, &mut subs);
        scope.insert("println", println_var);

        let assert_var = TyVar::uniq();
        let assert = Ty::func([Ty::bool()], Ty::null());
        unify(&Ty::Var(assert_var), &assert, &mut subs);
        scope.insert("assert", assert_var);

        Self { src, subs, scopes: vec![scope], named_types }
    }
}

impl FnScope {
    /// Returns none if name is ignored ("_")
    fn insert(&mut self, name: &'static str, ty: TyVar) -> Option<Ident> {
        if name == "_" {
            return None;
        }
        let ident = Ident { ty, local: self.variables.len() };
        let prev = self.variables.insert(name, ident);
        assert!(prev.is_none(), "{name}: {ident:?}");
        Some(ident)
    }
}

impl Lowering<'_> {
    /// Returns none if name is ignored  ("_")
    pub fn insert_scope(&mut self, name: &'static str, ty: TyVar) -> Option<Ident> {
        self.scope().insert(name, ty)
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
            Stmt::Function(func) => self.function(func, out)?,
            Stmt::Return(ret) => self.ret(ret, out)?,
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
        let iter_item_ty = TyVar::uniq();
        let item_ty = self.iter_item_ty(&iter_typ);
        unify(&Ty::Var(iter_item_ty), &item_ty, &mut self.subs);

        let iter_ident = self.insert_scope(&for_loop.ident, iter_item_ty);
        let body = self.block(&for_loop.body.stmts)?;

        // TODO: Handle for loop sugar here instead of later.
        out.push(Item::ForLoop(ForLoop { ident: iter_ident, iter, body }));
        Ok(())
    }

    fn if_chain(&mut self, if_chain: &ast::IfChain, out: &mut Vec<Item>) -> Result<()> {
        let mut chain = vec![];

        let condition = self.expr(&if_chain.first.condition)?;
        unify(&condition.ty, &Ty::bool(), &mut self.subs);
        let block = self.block(&if_chain.first.body.stmts)?;
        chain.push((condition, block));

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
        match iter.name {
            "range" => Ty::int(),
            "range_inclusive" => Ty::int(),
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
        assert!(!self.scope().variables.contains_key(ident));
        let var = TyVar::uniq();

        if let Some(expl_ty) = &var_decl.typ {
            let ty = self.load_explicit_type(expl_ty)?;
            unify(&ty, &Ty::Var(var), &mut self.subs);
        }

        if let Some(expr) = &var_decl.expr {
            let expr = self.expr(expr)?;
            unify(&expr.ty, &Ty::Var(var), &mut self.subs);
            out.push(Item::Assign(Assign { ident, expr }))
        }
        self.insert_scope(ident, var);
        Ok(())
    }

    fn assign(&mut self, assign: &ast::Assign, out: &mut Vec<Item>) -> Result<()> {
        let ident = *self.scope().variables.get(&**assign.root).unwrap();
        let expr = self.expr(&assign.expr)?;
        unify(&Ty::Var(ident.ty), &expr.ty, &mut self.subs);
        out.push(Item::Assign(Assign { ident: &assign.root, expr }));
        Ok(())
    }

    fn function(&mut self, func: &ast::Function, out: &mut Vec<Item>) -> Result<()> {
        let fn_var = TyVar::uniq();
        let ident = self.insert_scope(&func.ident, fn_var).unwrap();

        let ret_var = TyVar::uniq();
        self.scopes.push(FnScope { ret_var, variables: FxHashMap::default() });
        let mut params = vec![];
        for (ident, expl_typ) in &func.params {
            let ty = self.load_explicit_type(expl_typ)?;
            let var = TyVar::uniq();
            params.push(Ty::Var(var));
            unify(&Ty::Var(var), &ty, &mut self.subs);
            self.insert_scope(ident, var);
        }
        let fn_params = params.clone();
        params.push(Ty::Var(ret_var));

        if let Some(ret_ty) = &func.ret_type {
            let ret_ty = self.load_explicit_type(ret_ty)?;
            unify(&Ty::Var(ret_var), &ret_ty, &mut self.subs);
        } else {
            unify(&Ty::Var(ret_var), &Ty::null(), &mut self.subs);
        }

        // TODO: Is this the right way to explain a function type?
        let fn_ty = Ty::Con(TyCon { name: "func", generics: params.into() });
        unify(&Ty::Var(fn_var), &fn_ty, &mut self.subs);

        let body = self.block(&func.body.stmts)?;
        out.push(Item::Function(Function {
            name: &func.ident,
            ident,
            params: fn_params,
            ret: ret_var,
            body,
        }));
        self.scopes.pop().unwrap();
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
        let ty = self.named_types.get(&**expl_ty.ident).unwrap().clone();
        let Ty::Con(tycon) = ty else { panic!() };
        Ok(Ty::Con(TyCon {
            name: tycon.name,
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
            _ => todo!("{expr:?}"),
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
                Expr { ty: Ty::Var(ident.ty), kind: ExprKind::Ident(ident) }
            }
            _ => todo!(),
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
            Some(ident) => Some(*ident),
            None => self.scopes.first().unwrap().variables.get(name).copied(),
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
            BinOp::Eq => Ty::bool(),
            BinOp::Range => {
                unify(ty, &Ty::int(), &mut self.subs);
                Ty::range()
            }
            BinOp::RangeInclusive => {
                unify(ty, &Ty::int(), &mut self.subs);
                Ty::range_inclusive()
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

    fn fn_call(&mut self, func: &ast::Expr, args: &[Spanned<ast::Expr>]) -> Result<Expr> {
        // FIXME: Not entirely sure how to avoid substituting the type here.

        let expr = self.expr(func)?;
        let fn_ty = expr.ty.sub(&self.subs);
        let Ty::Con(TyCon { name, generics }) = fn_ty else { panic!() };
        assert_eq!(name, "func");
        assert_eq!(args.len() + 1, generics.len());
        let mut new_args = Vec::with_capacity(args.len());
        for (arg, param) in args.iter().zip(&*generics) {
            let arg = self.expr(arg)?;
            unify(&arg.ty, param, &mut self.subs);
            new_args.push(arg);
        }
        let ret = generics.last().unwrap().clone();
        Ok(Expr { ty: ret, kind: ExprKind::FnCall { expr: Box::new(expr), args: new_args } })
    }

    fn field_access(&mut self, expr: &ast::Expr, field: &'static str) -> Result<Expr> {
        let expr = self.expr(expr)?;
        let field_ty = self.field_ty(&expr.ty, field);
        Ok(Expr { ty: field_ty, kind: ExprKind::FieldAccess { expr: Box::new(expr), field } })
    }

    fn field_ty(&self, ty: &Ty, field: &'static str) -> Ty {
        let Ty::Con(tycon) = ty.sub(&self.subs) else { panic!() };
        match tycon.name {
            "array" => match field {
                "len" => Ty::int(),
                _ => todo!(),
            },
            _ => todo!(),
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
        match tycon.name {
            "array" => match method {
                "push" => Rc::new([tycon.generics[0].clone(), Ty::null()]),
                "pop" => Rc::new([tycon.generics[0].clone()]),
                "sort" => Rc::new([ty.clone()]),
                _ => todo!(),
            },
            _ => todo!(),
        }
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
                static CACHE: TyCon = TyCon { name: stringify!($name), generics: Rc::new([]) };
            }
            CACHE.with(|ty| Ty::Con(ty.clone()))
        })+

    };
}

impl Ty {
    impl_ty_const!(str, int, bool, char, null, range, range_inclusive);

    pub fn array(of: TyVar) -> Ty {
        Ty::Con(TyCon { name: "array", generics: Rc::new([Ty::Var(of)]) })
    }

    pub fn func(args: impl IntoIterator<Item = Ty>, ret: Ty) -> Ty {
        let args = args.into_iter().chain([ret]).collect();
        Ty::Con(TyCon { name: "func", generics: args })
    }
}
