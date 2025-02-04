use std::{
    collections::HashMap,
    fmt,
    iter::zip,
    rc::Rc,
    sync::atomic::{AtomicUsize, Ordering},
};

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Ty {
    Con(TyCon),
    Var(TyVar),
}

impl fmt::Debug for Ty {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Con(con) => con.fmt(f),
            Self::Var(var) => var.fmt(f),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TyCon {
    pub name: &'static str,
    pub generics: Rc<[Ty]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TyVar(pub usize);

pub type Substitutions = HashMap<TyVar, Ty>;

#[track_caller]
pub fn unify(left: &Ty, right: &Ty, subs: &mut Substitutions) {
    match (&left, &right) {
        (
            Ty::Con(TyCon { name: name1, generics: gen1 }),
            Ty::Con(TyCon { name: name2, generics: gen2 }),
        ) => {
            assert_eq!(name1, name2);
            assert_eq!(gen1.len(), gen2.len());

            for (l, r) in zip(gen1.iter(), gen2.iter()) {
                unify(l, r, subs);
            }
        }
        (Ty::Var(l), Ty::Var(r)) if l == r => {}
        (_, Ty::Var(v @ TyVar(_))) => insert(left, *v, subs),
        (Ty::Var(v @ TyVar(_)), _) => insert(right, *v, subs),
    }
}

#[track_caller]
fn insert(ty: &Ty, v: TyVar, subs: &mut Substitutions) {
    if let Some(sub) = subs.get(&v).cloned() {
        unify(ty, &sub, subs);
        return;
    }
    assert!(!v.occurs_in(ty, subs), "Infinite type.");
    subs.insert(v, ty.clone());
}

impl TyVar {
    pub fn uniq() -> Self {
        static COUNTER: AtomicUsize = AtomicUsize::new(0);
        Self(COUNTER.fetch_add(1, Ordering::Relaxed))
    }

    pub fn occurs_in(&self, ty: &Ty, subs: &Substitutions) -> bool {
        match ty {
            Ty::Var(v @ TyVar(i)) => {
                if let Some(sub) = subs.get(v) {
                    if *sub != Ty::Var(*v) {
                        return self.occurs_in(sub, subs);
                    }
                }
                self.0 == *i
            }
            Ty::Con(TyCon { generics, .. }) => {
                generics.iter().any(|generic| self.occurs_in(generic, subs))
            }
        }
    }
}

impl Ty {
    fn sub(&self, subs: &Substitutions) -> Ty {
        match self {
            Self::Con(TyCon { name, generics }) => {
                Ty::Con(TyCon { name, generics: generics.iter().map(|ty| ty.sub(subs)).collect() })
            }
            Self::Var(v @ TyVar(_)) => {
                if let Some(t) = subs.get(v) {
                    t.sub(subs)
                } else {
                    self.clone()
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    macro_rules! tyvar {
        ($i: expr) => {
            Ty::Var(TyVar($i))
        };
    }
    macro_rules! tycon {
        ($name:expr,$($generic:expr)*) => {
            Ty::Con(TyCon {
                name: $name,
                generics: vec![$($generic),*].into(),
            })
        };
        ($name:expr) => { tycon!($name,) };
    }
    #[test]
    fn test() {
        let mut subs = HashMap::new();

        unify(&tyvar!(3), &tycon!("array", tyvar!(5)), &mut subs);
        unify(&tyvar!(4), &tycon!("int"), &mut subs);
        unify(&tyvar!(4), &tyvar!(1), &mut subs);
        unify(&tyvar!(4), &tycon!("int"), &mut subs);
        unify(&tyvar!(3), &tycon!("array", tyvar!(6)), &mut subs);
        unify(&tyvar!(6), &tyvar!(4), &mut subs);
        unify(&tyvar!(3), &tyvar!(2), &mut subs);

        assert_eq!(tyvar!(1).sub(&subs), tycon!("int"));
        assert_eq!(tyvar!(2).sub(&subs), tycon!("array", tycon!("int")));
        assert_eq!(tyvar!(3).sub(&subs), tycon!("array", tycon!("int")));
        assert_eq!(tyvar!(4).sub(&subs), tycon!("int"));
        assert_eq!(tyvar!(5).sub(&subs), tycon!("int"));
        assert_eq!(tyvar!(6).sub(&subs), tycon!("int"));
    }
}
