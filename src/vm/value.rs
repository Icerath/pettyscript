use std::{cell::RefCell, cmp::Ordering, collections::BTreeMap, ops::Deref, rc::Rc};

use crate::builtints::Builtin;

pub type PettyMap<'src> = BTreeMap<Value<'src>, Value<'src>>;

// TODO: Remove Rc<Refcell> with indexes
// TODO: Replace BTreeMap with HashMap
// TODO: Avoid extra indirection/allocation for Struct.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Value<'src> {
    Bool(bool),
    EnumVariant { tag: u16 },
    Char(char),
    Int(i64),
    Callable(Callable),
    String(PettyStr<'src>),
    Array(Rc<RefCell<Vec<Value<'src>>>>),
    Map(Rc<RefCell<PettyMap<'src>>>),
    Range([i64; 2]),
    Struct { fields: Rc<RefCell<Box<[Value<'src>]>>> },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Callable {
    Builtin(Builtin),
    Function { label: u32, stack_size: u16 },
}

#[derive(Debug, Clone)]
pub enum PettyStr<'src> {
    Literal(&'src str),
    String(Rc<Box<str>>),
}

impl Deref for PettyStr<'_> {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        self.as_str()
    }
}

impl PartialEq for PettyStr<'_> {
    fn eq(&self, other: &Self) -> bool {
        self.as_str() == other.as_str()
    }
}

impl Eq for PettyStr<'_> {}

impl PartialOrd for PettyStr<'_> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.as_str().cmp(other.as_str()))
    }
}

impl Ord for PettyStr<'_> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_str().cmp(other.as_str())
    }
}

impl PettyStr<'_> {
    pub fn as_str(&self) -> &str {
        match *self {
            Self::Literal(str) => str,
            Self::String(ref str) => str,
        }
    }
}
