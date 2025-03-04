use crate::prelude::*;

#[derive(Default, Debug)]
pub struct TyCtx {
    subs: HashMap<TyVid, Ty>,
    ty_vid: u32,
    generic_id: u32,
    trait_id: u32,
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
    pub fn new_infer(&mut self) -> Ty {
        Ty::from(TyKind::Infer(InferTy::TyVar(self.vid())))
    }

    pub fn vid(&mut self) -> TyVid {
        self.ty_vid += 1;
        TyVid { index: self.ty_vid }
    }

    // TODO: Rework generics
    pub fn new_generic(&mut self, traits: Vec<TraitId>) -> Ty {
        Ty::from(TyKind::Generic { id: self.generic_id(), traits })
    }

    pub fn generic_id(&mut self) -> GenericId {
        self.generic_id += 1;
        GenericId { index: self.generic_id }
    }

    pub fn new_trait_id(&mut self) -> TraitId {
        self.trait_id += 1;
        TraitId { index: self.trait_id }
    }

    pub fn infer(&self, ty: &Ty) -> Ty {
        match ty.kind() {
            TyKind::Infer(InferTy::TyVar(var)) => self.infer(&self.subs[var]),
            _ => ty.clone(),
        }
    }

    pub fn eq(&mut self, lhs: &Ty, rhs: &Ty) {
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

    fn insert(&mut self, var: TyVid, ty: &Ty) {
        if let Some(sub) = self.subs.get(&var).cloned() {
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
                        return self.occurs_in(*var, sub);
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
