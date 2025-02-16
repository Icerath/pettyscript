use std::{
    collections::{BTreeMap, HashMap, HashSet},
    rc::Rc,
    sync::atomic::{AtomicU32, Ordering},
};

use miette::Result;
use rustc_hash::{FxHashMap, FxHashSet};

use crate::{
    builtints::Builtin,
    intern::intern,
    parser::{
        self as ast, BinOp, ExplicitType, ImplSig, Pat, Path, Spanned, Stmt, StructInitField,
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
    Assign(Assign),
    Continue,
    Break,
    Return(Return),
}

#[derive(Debug)]
pub struct Function {
    pub offset: Offset,
    pub params: Vec<Ident>,
    pub stack_size: usize,
    pub ret: Ty,
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
    pub segments: Vec<AssignSegment>,
    pub expr: Expr,
}

#[derive(Debug)]
pub enum AssignSegment {
    Field(u32),
    #[expect(unused)]
    Index(Expr),
}

#[derive(Debug)]
pub struct Return {
    pub expr: Option<Expr>,
    pub pops: usize,
}

#[derive(Debug)]
pub struct Expr {
    pub ty: Ty,
    pub kind: ExprKind,
}

impl Expr {
    pub fn ident(ident: Ident) -> Self {
        Self { ty: ident.ty, kind: ExprKind::LoadIdent { offset: ident.offset } }
    }
}

#[derive(Debug)]
pub enum ExprKind {
    Unary { expr: Box<Expr>, op: UnaryOp },
    Binary { exprs: Box<[Expr; 2]>, op: BinOp },
    FnCall { expr: Box<Expr>, args: Vec<Expr> },
    FieldAccess { expr: Box<Expr>, field: &'static str },
    MethodCall { expr: Box<Expr>, method: &'static str, args: Vec<Expr> },
    Index { expr: Box<Expr>, index: Box<Expr> },
    StructInit { fields: Vec<(u32, Expr)> },
    EnumVariant { tag: u16 },
    Array(Vec<Expr>),
    Tuple(Vec<Expr>),
    Map(Vec<[Expr; 2]>),
    LoadIdent { offset: Offset },
    Bool(bool),
    Char(char),
    Int(i64),
    Str(&'static str),
    Fstr(Fstr),
    // Temporary until generic impls are supported
    Format(Box<Expr>),
}

#[derive(Debug, Clone)]
struct Trait {
    expected_functions: Rc<[TraitFnSig]>,
}

#[derive(Debug)]
struct TraitFnSig {
    name: &'static str,
    params: Vec<ParamTy>,
    ret: ParamTy,
}

#[derive(Debug)]
enum ParamTy {
    Ty(Ty),
    Self_,
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
    pub segments: Vec<(&'static str, ExprKind)>,
    pub remaining: &'static str,
}

pub struct Lowering<'src> {
    named_types: FxHashMap<&'static str, Ty>,
    enums: FxHashMap<u32, EnumData>,
    methods: FxHashMap<(TyCon, &'static str), Ident>,
    traits: FxHashMap<&'static str, Trait>,
    trait_impls: FxHashSet<(TyCon, &'static str)>,
    pub main_fn: Option<Offset>,
    pub subs: Substitutions,
    impl_block: Option<ImplBlock>,
    scopes: Vec<FnScope>,
    #[expect(unused)]
    src: &'src str,
}

pub struct EnumData {
    name_map: Ident,
    variants: Rc<BTreeMap<&'static str, u16>>,
}

pub struct ImplBlock {
    ty: Ty,
}

#[derive(Debug)]
pub struct FnScope {
    ret_var: Ty,
    variables: FxHashMap<&'static str, Ident>,
    var_counter: usize,
    for_loops: usize,
}

impl<'src> Lowering<'src> {
    pub fn new(src: &'src str) -> Self {
        let subs = Substitutions::new();

        let mut named_types = HashMap::default();

        let generics = Rc::new([]);
        let builtin_types = [
            ("null", TyKind::Null),
            ("bool", TyKind::Bool),
            ("int", TyKind::Int),
            ("char", TyKind::Char),
            ("str", TyKind::Str),
            ("array", TyKind::Array),
            ("map", TyKind::Map),
            ("tuple", TyKind::Tuple),
        ];
        for (name, kind) in builtin_types {
            named_types.insert(name, Ty::Con(TyCon { kind, generics: generics.clone() }));
        }

        let mut scope = FnScope {
            ret_var: Ty::from(TyKind::Null),
            variables: FxHashMap::default(),
            for_loops: 0,
            var_counter: 0,
        };

        for builtin in Builtin::ALL {
            let name = builtin.name();
            let ty = match builtin {
                Builtin::Println => Ty::func([Ty::from(TyKind::Str)], Ty::from(TyKind::Null)),
                Builtin::Assert => Ty::func([Ty::from(TyKind::Bool)], Ty::from(TyKind::Bool)),
                Builtin::Exit => Ty::func([Ty::from(TyKind::Int)], Ty::from(TyKind::Null)),
                Builtin::ParseInt => Ty::func([Ty::from(TyKind::Str)], Ty::from(TyKind::Int)),
                Builtin::ReadFile => Ty::func([Ty::from(TyKind::Str)], Ty::from(TyKind::Str)),
            };
            scope.insert(name, ty, true);
        }

        scope.insert("null", Ty::from(TyKind::Null), true);

        Self {
            main_fn: None,
            src,
            subs,
            methods: HashMap::default(),
            traits: HashMap::default(),
            trait_impls: HashSet::default(),
            scopes: vec![scope],
            named_types,
            enums: HashMap::default(),
            impl_block: None,
        }
    }
}

impl FnScope {
    /// Returns none if name is ignored ("_")
    fn insert(&mut self, name: &'static str, ty: Ty, is_global: bool) -> Option<Ident> {
        if name == "_" {
            return None;
        }
        let offset = self.var_counter as u32;
        self.var_counter += 1;
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
            Stmt::Trait(trait_) => self.trait_(trait_, out)?,
            Stmt::WhileLoop(while_loop) => self.while_loop(while_loop, out)?,
            Stmt::ForLoop(for_loop) => self.for_loop(for_loop, out)?,
            Stmt::IfChain(if_chain) => self.if_chain(if_chain, out)?,
            Stmt::Let(var_decl) => self.var_decl(var_decl, false, out)?,
            Stmt::Const(var_decl) => self.var_decl(var_decl, true, out)?,
            Stmt::Assign(assign) => self.assign(assign, out)?,
            Stmt::ImplBlock(impl_) => self.impl_(impl_, out)?,
            Stmt::Struct(struct_) => self.struct_(struct_, out)?,
            Stmt::Enum(enum_) => self.enum_(enum_, out)?,
            Stmt::Function(func) => self.function(func, out)?,
            Stmt::Return(ret) => self.ret(ret, out)?,
            Stmt::Continue => out.push(Item::Continue),
            Stmt::Break => out.push(Item::Break),
            Stmt::Expr(expr) => out.push(Item::Expr(self.expr(expr)?)),
            Stmt::Block(block) => block.stmts.iter().try_for_each(|stmt| self.stmt(stmt, out))?,
        }
        Ok(())
    }

    fn trait_(&mut self, trait_: &ast::Trait, out: &mut Vec<Item>) -> Result<()> {
        _ = out;
        let mut expected_functions = vec![];

        for stmt in &trait_.body.stmts {
            match &**stmt {
                Stmt::Function(func) => {
                    assert!(func.generics.is_empty());
                    assert!(func.body.is_none());
                    let mut params = vec![];
                    for param in &func.params {
                        params.push(self.load_param_ty(&param.expl_ty)?);
                    }
                    let ret = match &func.ret_type {
                        Some(ret) => self.load_param_ty(ret)?,
                        None => ParamTy::Ty(Ty::from(TyKind::Null)),
                    };
                    expected_functions.push(TraitFnSig { name: *func.ident, params, ret });
                }
                _ => panic!("{stmt:?}"),
            }
        }
        self.traits.insert(trait_.name, Trait { expected_functions: expected_functions.into() });
        Ok(())
    }

    fn load_param_ty(&self, ty: &Spanned<ExplicitType>) -> Result<ParamTy> {
        if ty.is_self() { Ok(ParamTy::Self_) } else { self.load_explicit_type(ty).map(ParamTy::Ty) }
    }

    fn while_loop(&mut self, while_loop: &ast::WhileLoop, out: &mut Vec<Item>) -> Result<()> {
        let branch_expr = self.expr(&while_loop.expr)?;
        let branch_expr = Expr {
            ty: Ty::from(TyKind::Bool),
            kind: ExprKind::Unary { expr: Box::new(branch_expr), op: UnaryOp::Not },
        };
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
        self.scope().for_loops += 1;
        let iter = self.expr(&for_loop.iter)?;
        let Ty::Con(iter_typ) = iter.ty.sub(&self.subs) else { panic!() };
        let item_ty = Self::iter_item_ty(&iter_typ);

        let iter_ident = self.insert_scope(&for_loop.ident, item_ty);
        let body = self.block(&for_loop.body.stmts)?;

        // TODO: Handle for loop sugar here instead of later.
        out.push(Item::ForLoop(ForLoop { ident: iter_ident, iter, body }));
        self.scope().for_loops -= 1;
        Ok(())
    }

    fn if_chain(&mut self, if_chain: &ast::IfChain, out: &mut Vec<Item>) -> Result<()> {
        let mut chain = vec![];

        for if_stmt in [&if_chain.first].into_iter().chain(&if_chain.r#else_ifs) {
            let condition = self.expr(&if_stmt.condition)?;
            unify(&condition.ty, &Ty::from(TyKind::Bool), &mut self.subs);
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

    fn iter_item_ty(iter: &TyCon) -> Ty {
        // FIXME: .............
        match iter.kind {
            TyKind::Range | TyKind::RangeInclusive => Ty::from(TyKind::Int),
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
        let item = if *ident == "_" {
            Item::Expr(expr)
        } else {
            let segments = vec![];
            let ident = self.insert_scope(ident, ty).unwrap();
            Item::Assign(Assign { root: ident, segments, expr })
        };
        out.push(item);
        Ok(())
    }

    fn assign(&mut self, assign: &ast::Assign, out: &mut Vec<Item>) -> Result<()> {
        let mut var = self.load_var(&assign.root).unwrap().ty;
        let mut segments = Vec::with_capacity(assign.segments.len());
        for segment in &assign.segments {
            match segment {
                ast::AssignSegment::Index(_) => panic!(),
                ast::AssignSegment::Field(field) => {
                    var = var.sub(&self.subs);

                    let Ty::Con(tycon) = &var else { panic!() };
                    let TyKind::Struct { fields, .. } = &tycon.kind else { panic!() };
                    segments.push(AssignSegment::Field(fields.get(**field).unwrap().0));
                    var = self.field_ty(&var, field);
                }
            }
        }
        let expr = self.expr(&assign.expr)?;
        unify(&var, &expr.ty, &mut self.subs);

        let root = self.load_var(&assign.root).unwrap();
        // TODO: Assignment should pass all segments
        out.push(Item::Assign(Assign { root, segments, expr }));
        Ok(())
    }

    fn impl_(&mut self, impl_: &ast::ImplBlock, out: &mut Vec<Item>) -> Result<()> {
        assert!(self.impl_block.is_none());
        match &*impl_.sig {
            ImplSig::Inherent(sig) => self.inherent_impl(sig, &impl_.body, out),
            ImplSig::Trait(sig) => self.trait_impl(sig, &impl_.body, out),
        }
    }

    fn inherent_impl(
        &mut self,
        expl_ty: &Spanned<ExplicitType>,
        body: &ast::Block,
        out: &mut Vec<Item>,
    ) -> Result<()> {
        let ty = self.load_explicit_type(expl_ty)?;
        self.impl_block = Some(ImplBlock { ty });
        body.stmts.iter().try_for_each(|stmt| self.stmt(stmt, out))?;
        self.impl_block = None;
        Ok(())
    }

    fn trait_impl(
        &mut self,
        [trait_, expl_ty]: &[Spanned<ExplicitType>; 2],
        body: &ast::Block,
        out: &mut Vec<Item>,
    ) -> Result<()> {
        let ty = self.load_explicit_type(expl_ty)?;
        let Ty::Con(ty) = ty else { panic!() };
        self.impl_block = Some(ImplBlock { ty: Ty::Con(ty.clone()) });

        let trait_ident = *trait_.ident;
        let trait_ = self.traits.get(trait_ident).unwrap().clone();
        // TODO: Don't be dependant on order.
        for (impl_item, stmt) in trait_.expected_functions.iter().zip(&body.stmts) {
            let Stmt::Function(func) = &**stmt else { panic!() };
            assert_eq!(impl_item.name, *func.ident);
            for (expected, param) in impl_item.params.iter().zip(&func.params) {
                let param_ty = self.load_explicit_type(&param.expl_ty)?;
                let Ty::Con(param_ty) = param_ty else { panic!() };
                let expected_ty = match expected {
                    ParamTy::Self_ => &ty,
                    ParamTy::Ty(Ty::Con(ty)) => ty,
                    ParamTy::Ty(Ty::Var(..)) => panic!(),
                };
                assert_eq!(param_ty, *expected_ty);
            }
            let ret_ty = match &func.ret_type {
                Some(expl_ty) => self.load_explicit_type(expl_ty)?,
                None => Ty::from(TyKind::Null),
            };
            let Ty::Con(ret_ty) = ret_ty else { panic!() };
            let expected_ty = match &impl_item.ret {
                ParamTy::Self_ => &ty,
                ParamTy::Ty(Ty::Con(ty)) => ty,
                ParamTy::Ty(Ty::Var(..)) => panic!(),
            };
            assert_eq!(ret_ty, *expected_ty);
            self.function(func, out)?;
        }
        self.trait_impls.insert((ty, trait_ident));
        self.impl_block = None;
        Ok(())
    }

    fn struct_(&mut self, struct_: &ast::Struct, out: &mut Vec<Item>) -> Result<()> {
        let mut fields = BTreeMap::new();
        for (field_id, param) in struct_.fields.iter().enumerate() {
            let ty = self.load_explicit_type(&param.expl_ty)?;
            fields.insert(*param.ident, (field_id as u32, ty));
        }
        let fields = Rc::new(fields);
        let ty = Ty::Con(TyCon { kind: TyKind::Struct { fields }, generics: Rc::new([]) });
        let prev = self.named_types.insert(&struct_.ident, ty);
        assert!(prev.is_none());
        _ = out;
        Ok(())
    }

    fn enum_(&mut self, enum_: &ast::Enum, out: &mut Vec<Item>) -> Result<()> {
        static ENUM_ID: AtomicU32 = AtomicU32::new(0);
        let enum_id = ENUM_ID.fetch_add(1, Ordering::Relaxed);

        let mut variants = BTreeMap::<&str, _>::new();
        assert!(enum_.variants.len() < u16::MAX as usize);
        for (offset, field) in (0u16..).zip(&enum_.variants) {
            variants.insert(field, offset);
        }
        let variants = Rc::new(variants);
        let name_map = self.create_enum_name_map(enum_, out);
        self.enums.insert(enum_id, EnumData { name_map, variants: variants.clone() });

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

    fn create_enum_name_map(&mut self, enum_: &ast::Enum, out: &mut Vec<Item>) -> Ident {
        let array = ExprKind::Array(
            enum_
                .variants
                .iter()
                .map(|variant| Expr { ty: Ty::from(TyKind::Str), kind: ExprKind::Str(variant) })
                .collect(),
        );
        let expr = Expr { ty: Ty::array(Ty::from(TyKind::Str)), kind: array };
        let name = intern(&format!("{}_variants", *enum_.ident));
        let ident = self.insert_scope(name, expr.ty.clone()).unwrap();
        out.push(Item::Assign(Assign { root: ident.clone(), segments: vec![], expr }));
        ident
    }

    fn function(&mut self, func: &ast::Function, out: &mut Vec<Item>) -> Result<()> {
        let ret = if let Some(ret_ty) = &func.ret_type {
            self.load_explicit_type(ret_ty)?
        } else {
            Ty::from(TyKind::Null)
        };
        self.scopes.push(FnScope {
            ret_var: ret.clone(),
            variables: FxHashMap::default(),
            var_counter: 0,
            for_loops: 0,
        });
        let mut params = vec![];
        for param in &func.params {
            let ty = self.load_explicit_type(&param.expl_ty)?;
            let ident = self.insert_scope(&param.ident, ty).unwrap();
            params.push(ident);
        }
        let fn_params = params.clone();

        let fn_ty = Ty::Con(TyCon::from(TyKind::Function {
            params: params.iter().map(|ident| ident.ty.clone()).collect(),
            ret: Rc::new(ret.clone()),
        }));

        let ident = if self.impl_block.is_none() {
            let scope = self.scopes.pop().unwrap();
            let ident = self.insert_scope(&func.ident, fn_ty.clone()).unwrap();
            self.scopes.push(scope);
            ident
        } else {
            let offset = self.scopes[0].var_counter;
            let ident = Ident { offset: Offset::Global(offset as u32), ty: fn_ty.clone() };
            self.scopes[0].var_counter += 1;
            ident
        };

        if *func.ident == "main" {
            assert!(params.is_empty());
            // TODO: Assert ret is null
            self.main_fn = Some(ident.offset);
        }

        if let Some(impl_block) = &self.impl_block {
            let Ty::Con(ty) = impl_block.ty.sub(&self.subs) else { panic!() };
            self.methods.insert((ty, *func.ident), ident.clone());
        }
        let body = self.block(&func.body.as_ref().unwrap().stmts)?;

        let last_scope = self.scopes.pop().unwrap();
        let stack_size = last_scope.variables.len();

        out.push(Item::Function(Function {
            offset: ident.offset,
            stack_size,
            params: fn_params,
            ret,
            body,
        }));
        Ok(())
    }

    fn ret(&mut self, ret: &ast::Return, out: &mut Vec<Item>) -> Result<()> {
        let ret_var = self.scope().ret_var.clone();

        let expr = if let Some(expr) = &ret.0 {
            let expr = self.expr(expr)?;
            unify(&expr.ty, &ret_var, &mut self.subs);
            Some(expr)
        } else {
            unify(&Ty::from(TyKind::Null), &ret_var, &mut self.subs);
            None
        };
        let pops = self.scope().for_loops;

        out.push(Item::Return(Return { expr, pops }));
        Ok(())
    }

    fn load_explicit_type(&self, expl_ty: &Spanned<ExplicitType>) -> Result<Ty> {
        if expl_ty.is_inferred() {
            return Ok(Ty::Var(TyVar::uniq()));
        } else if expl_ty.is_self() {
            return Ok(self.impl_block.as_ref().unwrap().ty.clone());
        }
        let ty =
            self.named_types.get(*expl_ty.ident).unwrap_or_else(|| panic!("{expl_ty:?}")).clone();
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
            ast::Expr::Path(path) => self.load_path(path),
            ast::Expr::Literal(literal) => self.literal(literal),
            ast::Expr::Unary { op, expr } => self.unary(*op, expr),
            ast::Expr::Binary { op, exprs } => self.binary(*op, &exprs[0], &exprs[1]),
            ast::Expr::Array(exprs) => self.array(exprs),
            ast::Expr::FnCall { function, args } => self.fn_call(function, args),
            ast::Expr::FieldAccess { expr, field } => self.field_access(expr, field),
            ast::Expr::MethodCall { expr, method, args } => self.method_call(expr, method, args),
            ast::Expr::Index { expr, index } => self.index(expr, index),
            ast::Expr::InitStruct { path, fields } => self.init_struct(path, fields),
        }
    }

    fn load_path(&mut self, path: &Path) -> Result<Expr> {
        let mut segments = path.segments.iter();
        let root = segments.next().expect("Paths should always be >= length 1");
        if path.segments.len() == 1 {
            let root = self.load_var(root).unwrap_or_else(|| panic!("{path:?}"));
            return Ok(Expr::ident(root));
        }
        let root = self.named_types.get(root).unwrap();
        let next = segments.next().unwrap();
        let Ty::Con(ty) = root.sub(&self.subs) else { panic!() };
        if let TyKind::Variant { id } = ty.kind {
            let enum_ = self.enums.get(&id).unwrap();
            let variant = *enum_.variants.get(next).unwrap();
            Ok(Expr {
                ty: Ty::Con(TyCon::from(TyKind::Variant { id })),
                kind: ExprKind::EnumVariant { tag: variant },
            })
        } else {
            let method = self.methods.get(&(ty, next)).unwrap().clone();
            Ok(Expr::ident(method))
        }
    }

    fn literal(&mut self, literal: &ast::Literal) -> Result<Expr> {
        Ok(match literal {
            ast::Literal::Bool(bool) => {
                Expr { ty: Ty::from(TyKind::Bool), kind: ExprKind::Bool(*bool) }
            }
            ast::Literal::Int(int) => Expr { ty: Ty::from(TyKind::Int), kind: ExprKind::Int(*int) },
            ast::Literal::Char(char) => {
                Expr { ty: Ty::from(TyKind::Char), kind: ExprKind::Char(*char) }
            }
            ast::Literal::String(str) => {
                Expr { ty: Ty::from(TyKind::Str), kind: ExprKind::Str(str) }
            }
            ast::Literal::FString(fstring) => self.fstr(fstring)?,

            ast::Literal::Map(map) => self.map(map)?,
            ast::Literal::Tuple(tuple) => self.tuple(tuple)?,
        })
    }

    fn fstr(&mut self, fstring: &ast::FString) -> Result<Expr> {
        let mut segments = vec![];
        for (str, aexpr) in &fstring.segments {
            let expr = self.expr(aexpr)?;
            let Ty::Con(tycon) = expr.ty.sub(&self.subs) else { panic!() };
            let expr = match &tycon.kind {
                // TODO: Don't support arrays/maps/tuples here.
                TyKind::Int
                | TyKind::Char
                | TyKind::Bool
                | TyKind::Str
                | TyKind::Array
                | TyKind::Map
                | TyKind::Tuple => ExprKind::Format(Box::new(expr)),
                TyKind::Variant { id } => self.enum_variant_str(expr, *id),
                _ => {
                    assert!(self.trait_impls.contains(&(tycon.clone(), "Display")), "{tycon:?}");
                    let method = self.methods.get(&(tycon, "to_str")).unwrap();
                    ExprKind::FnCall {
                        expr: Box::new(Expr::ident(method.clone())),
                        args: vec![expr],
                    }
                }
            };

            segments.push((*str, expr));
        }
        let remaining = fstring.remaining;
        Ok(Expr { ty: Ty::from(TyKind::Str), kind: ExprKind::Fstr(Fstr { segments, remaining }) })
    }

    fn enum_variant_str(&mut self, expr: Expr, id: u32) -> ExprKind {
        let ident = self.enums[&id].name_map.clone();
        let index = Expr {
            ty: Ty::from(TyKind::Int),
            kind: ExprKind::Unary { expr: Box::new(expr), op: UnaryOp::EnumTag },
        };
        ExprKind::Index { expr: Box::new(Expr::ident(ident)), index: Box::new(index) }
    }

    fn scope(&mut self) -> &mut FnScope {
        self.scopes.last_mut().unwrap()
    }

    fn load_var(&mut self, name: &'static str) -> Option<Ident> {
        match self.scopes.last().unwrap().variables.get(&name) {
            Some(ident) => Some(ident.clone()),
            None => self.scopes.first().unwrap().variables.get(&name).cloned(),
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
        let Ty::Con(tycon) = ty.sub(&self.subs) else { panic!() };

        macro_rules! ret {
            ($method:literal) => {{
                // TODO: Keep track of trait methods.
                let fn_ty = &self.methods.get(&(tycon, $method)).unwrap().ty;
                let Ty::Con(fn_tycon) = fn_ty.sub(&self.subs) else { panic!() };
                let TyKind::Function { ret, .. } = &fn_tycon.kind else { panic!() };
                ret.as_ref().clone()
            }};
        }

        match op {
            BinOp::Add => ret!("add"),
            BinOp::Sub => ret!("sub"),
            BinOp::Mul => ret!("mul"),
            BinOp::Div => ret!("div"),
            BinOp::Mod => ret!("mod"),
            BinOp::Eq | BinOp::Neq | BinOp::Less | BinOp::Greater => Ty::from(TyKind::Bool),
            BinOp::Range => {
                unify(ty, &Ty::from(TyKind::Int), &mut self.subs);
                Ty::from(TyKind::Range)
            }
            BinOp::RangeInclusive => {
                unify(ty, &Ty::from(TyKind::Int), &mut self.subs);
                Ty::from(TyKind::RangeInclusive)
            }
            BinOp::And | BinOp::Or => {
                unify(ty, &Ty::from(TyKind::Bool), &mut self.subs);
                Ty::from(TyKind::Bool)
            }
            _ => todo!("{op:?}"),
        }
    }

    fn array(&mut self, aexprs: &[ast::Expr]) -> Result<Expr> {
        let var = TyVar::uniq();
        let ty = Ty::array(Ty::Var(var));

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
        let ty = Ty::map(Ty::Var(key_ty), Ty::Var(value_ty));
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
            TyKind::Struct { fields, .. } => fields.get(field).unwrap().1.clone(),
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

        if let Some(params) = self.method_params(&expr.ty, method) {
            assert_eq!(args.len() + 1, params.len());
            let mut new_args = Vec::with_capacity(args.len());
            for (arg, param) in args.iter().zip(&*params) {
                let arg = self.expr(arg)?;
                unify(&arg.ty, param, &mut self.subs);
                new_args.push(arg);
            }
            let ret = params.last().unwrap().clone();
            return Ok(Expr {
                ty: ret,
                kind: ExprKind::MethodCall { expr: Box::new(expr), method, args: new_args },
            });
        }

        let Ty::Con(expr_ty) = expr.ty.sub(&self.subs) else { panic!() };
        let ident = self.methods.get(&(expr_ty, method)).expect(method).clone();
        let Ty::Con(tycon) = ident.ty.sub(&self.subs) else { panic!() };
        let TyKind::Function { params, ret } = &tycon.kind else { panic!() };

        assert_eq!(args.len() + 1, params.len());
        let mut new_args = Vec::with_capacity(args.len() + 1);
        new_args.push(expr);
        for (arg, param) in args.iter().zip(&**params) {
            let arg = self.expr(arg)?;
            unify(&arg.ty, param, &mut self.subs);
            new_args.push(arg);
        }

        Ok(Expr {
            ty: ret.as_ref().clone(),
            kind: ExprKind::FnCall { expr: Box::new(Expr::ident(ident)), args: new_args },
        })
    }

    #[expect(clippy::match_same_arms)]
    fn method_params(&mut self, ty: &Ty, method: &'static str) -> Option<Rc<[Ty]>> {
        let Ty::Con(tycon) = ty.sub(&self.subs) else { panic!() };
        Some(match &tycon.kind {
            TyKind::Int => match method {
                "abs" => Rc::new([Ty::from(TyKind::Int)]),
                _ => return None,
            },
            TyKind::Char => match method {
                "is_digit" => Rc::new([Ty::from(TyKind::Bool)]),
                "is_alphabetic" => Rc::new([Ty::from(TyKind::Bool)]),
                _ => return None,
            },
            TyKind::Str => match method {
                "lines" => Rc::new([Ty::array(Ty::from(TyKind::Str))]),
                "trim" => Rc::new([Ty::from(TyKind::Str)]),
                "starts_with" => Rc::new([Ty::from(TyKind::Str), Ty::from(TyKind::Bool)]),
                "is_digit" => Rc::new([Ty::from(TyKind::Bool)]),
                "is_alphabetic" => Rc::new([Ty::from(TyKind::Bool)]),
                "len" => Rc::new([Ty::from(TyKind::Int)]),
                _ => return None,
            },
            TyKind::Array => match method {
                "push" => Rc::new([tycon.generics[0].clone(), Ty::from(TyKind::Null)]),
                "pop" => Rc::new([tycon.generics[0].clone()]),
                "sort" => Rc::new([ty.clone()]),
                "len" => Rc::new([Ty::from(TyKind::Int)]),
                _ => return None,
            },
            TyKind::Map => match method {
                "insert" => Rc::new([
                    tycon.generics[0].clone(),
                    tycon.generics[1].clone(),
                    Ty::from(TyKind::Null),
                ]),
                "get" => Rc::new([tycon.generics[0].clone(), tycon.generics[1].clone()]),
                "contains" => Rc::new([tycon.generics[0].clone(), Ty::from(TyKind::Bool)]),
                "remove" => Rc::new([tycon.generics[0].clone(), Ty::from(TyKind::Null)]),
                _ => return None,
            },
            _ => return None,
        })
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

        match (&ty.kind, &index.kind) {
            (TyKind::Array, TyKind::Int) => ty.generics[0].clone(),
            (TyKind::Array, TyKind::Range) => Ty::Con(ty),
            (TyKind::Str, TyKind::Int) => Ty::from(TyKind::Char),
            (TyKind::Str, TyKind::Range) => Ty::from(TyKind::Str),
            _ => todo!("{ty:?}"),
        }
    }

    fn init_struct(&mut self, path: &Path, init_fields: &[StructInitField]) -> Result<Expr> {
        assert!(path.segments.len() == 1);
        let Ty::Con(tycon) = self.named_types.get(&path.segments[0]).unwrap().clone() else {
            panic!()
        };
        let TyKind::Struct { fields, .. } = tycon.kind else { panic!() };
        let mut new_fields = vec![];
        for init in init_fields {
            let (field_offset, ty) = &fields.get(*init.ident).unwrap();
            let init_expr = match init.expr.as_ref() {
                Some(expr) => {
                    let expr = self.expr(expr)?;
                    unify(ty, &expr.ty, &mut self.subs);
                    expr
                }
                None => Expr::ident(self.load_var(&init.ident).expect(&init.ident)),
            };
            new_fields.push((*field_offset, init_expr));
        }
        let ty = Ty::Con(TyCon { kind: TyKind::Struct { fields }, generics: Rc::new([]) });
        Ok(Expr { ty, kind: ExprKind::StructInit { fields: new_fields } })
    }
}

impl Ty {
    pub fn array(of: Ty) -> Ty {
        Ty::Con(TyCon { kind: TyKind::Array, generics: Rc::new([of]) })
    }

    pub fn map(key: Ty, val: Ty) -> Ty {
        Ty::Con(TyCon { kind: TyKind::Map, generics: Rc::new([key, val]) })
    }

    pub fn func(params: impl IntoIterator<Item = Ty>, ret: Ty) -> Ty {
        Ty::Con(TyCon::from(TyKind::Function {
            params: params.into_iter().collect(),
            ret: Rc::new(ret),
        }))
    }

    pub fn tuple(generics: Rc<[Ty]>) -> Ty {
        Ty::Con(TyCon { kind: TyKind::Tuple, generics })
    }
}
