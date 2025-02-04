use std::rc::Rc;

use miette::Result;
use rustc_hash::FxHashMap;

use crate::{
    parser::{self as ast, BinOp, ExplicitType, Pat, Spanned, Stmt, UnaryOp, VarDecl},
    typck::{Substitutions, Ty, TyCon, TyVar, unify},
};

#[derive(Debug)]
pub struct Block {
    items: Vec<Item>,
}

impl Block {
    const EMPTY: Self = Self { items: vec![] };
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
pub enum Item {
    Loop(Block),
    IfChain(IfChain),
    Expr(Expr),
    Block(Block),
    Assign(Assign),
    Continue,
    Break,
    Return(Return),
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
    local: u32,
}

#[derive(Debug)]
pub struct Fstr {
    pub segments: Vec<(&'static str, Expr)>,
    pub remaining: &'static str,
}

pub struct Lowering<'src> {
    pub named_types: FxHashMap<&'static str, Ty>,
    pub subs: Substitutions,
    scopes: Vec<FxHashMap<&'static str, Ident>>,
    src: &'src str,
}

impl<'src> Lowering<'src> {
    pub fn new(src: &'src str) -> Self {
        let subs = Substitutions::new();
        let scopes = vec![FxHashMap::default()];
        let mut named_types = FxHashMap::default();
        named_types.insert("int", Ty::int());
        named_types.insert("char", Ty::char());
        named_types.insert("bool", Ty::bool());
        named_types.insert("str", Ty::str());

        Self { src, subs, scopes, named_types }
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
            Stmt::WhileLoop(ast::WhileLoop { expr, body }) => {
                let branch_expr = self.expr(expr)?;
                let exit_condition = Item::IfChain(IfChain {
                    chain: vec![(branch_expr, Block { items: vec![Item::Break] })],
                    end: Block::EMPTY,
                });
                let mut new_body = vec![exit_condition];
                new_body.append(&mut self.block(&body.stmts)?.items);
                out.push(Item::Loop(Block { items: new_body }));
            }
            Stmt::Let(var_decl) => self.var_decl(var_decl, false, out)?,
            Stmt::Const(var_decl) => self.var_decl(var_decl, true, out)?,
            Stmt::Assign(assign) => self.assign(assign, out)?,
            Stmt::Expr(expr) => out.push(Item::Expr(self.expr(expr)?)),
            _ => todo!("{stmt:?}"),
        }
        Ok(())
    }

    fn var_decl(
        &mut self,
        var_decl: &Spanned<VarDecl>,
        is_const: bool,
        out: &mut Vec<Item>,
    ) -> Result<()> {
        let _ = is_const;
        let Pat::Ident(ident) = &*var_decl.pat else { todo!() };
        assert!(!self.scope().contains_key(ident));
        let var = TyVar::uniq();
        let offset = self.scope().len() as u32;

        if let Some(expl_ty) = &var_decl.typ {
            let ty = self.load_explicit_type(expl_ty)?;
            unify(&ty, &Ty::Var(var), &mut self.subs);
        }

        if let Some(expr) = &var_decl.expr {
            let expr = self.expr(expr)?;
            unify(&expr.ty, &Ty::Var(var), &mut self.subs);
            out.push(Item::Assign(Assign { ident, expr }))
        }
        self.scope().insert(ident, Ident { ty: var, local: offset });
        Ok(())
    }

    fn assign(&mut self, assign: &ast::Assign, out: &mut Vec<Item>) -> Result<()> {
        let ident = *self.scope().get(&**assign.root).unwrap();
        let expr = self.expr(&assign.expr)?;
        unify(&Ty::Var(ident.ty), &expr.ty, &mut self.subs);
        out.push(Item::Assign(Assign { ident: &assign.root, expr }));
        Ok(())
    }

    fn load_explicit_type(&self, expl_ty: &Spanned<ExplicitType>) -> Result<Ty> {
        Ok(self.named_types.get(&**expl_ty.ident).unwrap().clone())
    }

    fn expr(&mut self, expr: &ast::Expr) -> Result<Expr> {
        match expr {
            ast::Expr::Literal(literal) => self.literal(literal),
            ast::Expr::Unary { op, expr } => self.unary(*op, expr),
            ast::Expr::Binary { op, exprs } => self.binary(*op, &exprs[0], &exprs[1]),
            ast::Expr::Array(exprs) => self.array(exprs),
            _ => todo!(),
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
                let ident = self.scope().get(ident).unwrap();
                Expr { ty: Ty::Var(ident.ty), kind: ExprKind::Ident(*ident) }
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

    fn scope(&mut self) -> &mut FxHashMap<&'static str, Ident> {
        self.scopes.last_mut().unwrap()
    }

    fn unary(&mut self, op: UnaryOp, aexpr: &ast::Expr) -> Result<Expr> {
        let expr = self.expr(aexpr)?;
        Ok(Expr { ty: expr.ty.clone(), kind: ExprKind::Unary { expr: Box::new(expr), op } })
    }

    fn binary(&mut self, op: BinOp, left: &ast::Expr, right: &ast::Expr) -> Result<Expr> {
        let left = self.expr(left)?;
        let right = self.expr(right)?;
        unify(&left.ty, &right.ty, &mut self.subs);
        Ok(Expr::uniq(ExprKind::Binary { exprs: Box::new([left, right]), op }))
    }

    fn array(&mut self, aexprs: &[ast::Expr]) -> Result<Expr> {
        let var = TyVar::uniq();
        let ty = Ty::array(var);
        self.subs.insert(TyVar::uniq(), ty.clone());

        let mut exprs = vec![];
        for aexpr in aexprs {
            let expr = self.expr(aexpr)?;
            unify(&Ty::Var(var), &expr.ty, &mut self.subs);
            exprs.push(expr);
        }
        Ok(Expr { kind: ExprKind::Array(exprs), ty })
    }
}

impl Expr {
    fn uniq(kind: ExprKind) -> Self {
        Self { kind, ty: Ty::Var(TyVar::uniq()) }
    }
}

macro_rules! impl_ty_const {
    ($name: ident) => {
        pub fn $name() -> Ty {
            thread_local! {
                static CACHE: TyCon = TyCon { name: stringify!($name), generics: Rc::new([]) };
            }
            CACHE.with(|ty| Ty::Con(ty.clone()))
        }
    };
}

impl Ty {
    impl_ty_const!(str);

    impl_ty_const!(int);

    impl_ty_const!(bool);

    impl_ty_const!(char);

    pub fn array(of: TyVar) -> Ty {
        Ty::Con(TyCon { name: "array", generics: Rc::new([Ty::Var(of)]) })
    }
}
