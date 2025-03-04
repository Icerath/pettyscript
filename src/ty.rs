use std::{
    cell::{Cell, RefCell},
    hash::Hash,
};

use crate::prelude::*;

#[derive(Default, Debug)]
pub struct TyCtx {
    subs: SharedMap<TyVid, Ty>,
    ty_vid: Cell<u32>,
    generic_id: Cell<u32>,
    trait_id: Cell<u32>,
}

#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Ty {
    kind: Rc<TyKind>,
}

impl Ty {
    pub fn kind(&self) -> &TyKind {
        &self.kind
    }

    pub fn with_generics(&self, generics: Vec<Ty>) -> Self {
        // FIXME: shouln't ignore the existing generics
        match self.kind() {
            _ if generics.is_empty() => self.clone(),
            TyKind::Array(_) => TyKind::Array(generics[0].clone()).into(),
            TyKind::Map([_, _]) => TyKind::Map([generics[0].clone(), generics[1].clone()]).into(),
            TyKind::Tuple(_) => TyKind::Tuple(generics).into(),
            _ => todo!(),
        }
    }
}

impl From<TyKind> for Ty {
    fn from(kind: TyKind) -> Self {
        Self { kind: Rc::new(kind) }
    }
}

impl From<TyVid> for Ty {
    fn from(ty_vid: TyVid) -> Self {
        Self { kind: Rc::new(TyKind::Infer(InferTy::TyVar(ty_vid))) }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum InferTy {
    TyVar(TyVid),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TyVid {
    index: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct GenericId {
    index: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct TraitId {
    index: u32,
}

#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TyKind {
    Null,
    Bool,
    Int,
    Char,
    Str,
    Range,
    RangeInclusive,
    Array(Ty),
    Map([Ty; 2]),
    Tuple(Vec<Ty>),
    Struct { fields: BTreeMap<&'static str, (u32, Ty)> },
    Enum { id: u32, name: &'static str, variants: BTreeMap<&'static str, u16> },
    Function { params: Vec<Ty>, ret: Ty, generics: Vec<Ty> },
    Variant { id: u32 },
    Generic { id: GenericId, traits: Vec<TraitId> },
    Vtable { traits: Vec<TraitId> },
    Infer(InferTy),
}

impl TyCtx {
    pub fn new_infer(&self) -> Ty {
        Ty::from(TyKind::Infer(InferTy::TyVar(self.vid())))
    }

    pub fn vid(&self) -> TyVid {
        TyVid { index: self.ty_vid.update(|v| v + 1) }
    }

    // TODO: Rework generics
    pub fn new_generic(&self, traits: Vec<TraitId>) -> Ty {
        Ty::from(TyKind::Generic { id: self.generic_id(), traits })
    }

    pub fn generic_id(&self) -> GenericId {
        GenericId { index: self.generic_id.update(|v| v + 1) }
    }

    pub fn new_trait_id(&self) -> TraitId {
        TraitId { index: self.trait_id.update(|v| v + 1) }
    }

    pub fn infer(&self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Infer(InferTy::TyVar(var)) => self.infer(&self.subs.get(var).unwrap()),
            _ => ty.clone(),
        }
    }

    pub fn eq(&self, lhs: &Ty, rhs: &Ty) {
        match (lhs.kind(), rhs.kind()) {
            // Inference
            (TyKind::Infer(InferTy::TyVar(l)), TyKind::Infer(InferTy::TyVar(r))) if l == r => {}
            (TyKind::Infer(InferTy::TyVar(var)), _) => self.insert(*var, rhs),
            (_, TyKind::Infer(InferTy::TyVar(var))) => self.insert(*var, lhs),
            // Generics
            (TyKind::Array(lhs), TyKind::Array(rhs)) => self.eq(lhs, rhs),
            (TyKind::Map([lkey, lval]), TyKind::Map([rkey, rval])) => {
                self.eq(lkey, rkey);
                self.eq(lval, rval);
            }
            // other
            (lhs, rhs) => assert_eq!(lhs, rhs),
        }
    }

    fn insert(&self, var: TyVid, ty: &Ty) {
        if let Some(sub) = self.subs.get(&var) {
            self.eq(ty, &sub);
            return;
        }
        assert!(!self.occurs_in(var, ty), "Infinite type: {var:?} - {ty:?}");
        self.subs.insert(var, ty.clone());
    }

    fn occurs_in(&self, this: TyVid, ty: &Ty) -> bool {
        match ty.kind() {
            TyKind::Infer(InferTy::TyVar(var)) => {
                if let Some(sub) = self.subs.get(var) {
                    if *sub.kind() != TyKind::Infer(InferTy::TyVar(*var)) {
                        return self.occurs_in(*var, &sub);
                    }
                }
                this == *var
            }
            _ => false,
        }
    }
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.kind, f)
    }
}

struct SharedMap<K, V> {
    inner: RefCell<HashMap<K, V>>,
}

impl<K, V> Default for SharedMap<K, V> {
    fn default() -> Self {
        Self { inner: RefCell::default() }
    }
}

impl<K: fmt::Debug, V: fmt::Debug> fmt::Debug for SharedMap<K, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&*self.inner.borrow(), f)
    }
}

impl<K, V> SharedMap<K, V>
where
    K: Hash + Eq,
{
    fn insert(&self, key: K, val: V) {
        self.inner.borrow_mut().insert(key, val);
    }

    fn get<Q>(&self, key: &Q) -> Option<V>
    where
        Q: Hash + Eq,
        K: std::borrow::Borrow<Q>,
        V: Clone,
    {
        self.inner.borrow().get(key).cloned()
    }
}
