use std::{cell::RefCell, rc::Rc};

use crate::vm::{Callable, PettyMap, PettyStr, Value};

#[derive(
    macros::NumVariants, macros::AllVariants, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord,
)]
#[repr(u16)]
pub enum Builtin {
    Println,
    ReadFile,
    Exit,
    Assert,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum MethodBuiltin {
    StrTrim { trimmed: Rc<Box<str>> },
    StrStartsWith(PettyStr),
    StrIsDigit(PettyStr),
    StrIsAlphabetic(PettyStr),
    CharIsDigit(char),
    CharIsAlphabetic(char),
    MapGet(Rc<RefCell<PettyMap>>),
    MapInsert(Rc<RefCell<PettyMap>>),
    MapRemove(Rc<RefCell<PettyMap>>),
    ArrayPush(Rc<RefCell<Vec<Value>>>),
    ArrayPop(Rc<RefCell<Vec<Value>>>),
}

impl From<MethodBuiltin> for Value {
    fn from(value: MethodBuiltin) -> Self {
        Self::Callable(Callable::MethodBuiltin(value))
    }
}

#[derive(macros::NumVariants, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u16)]
pub enum BuiltinField {
    StrLen,
    StrTrim,
    StrStartsWith,
    StrIsDigit,
    StrIsAlphabetic,

    CharIsDigit,
    CharIsAlphabetic,

    ArrayPush,
    ArrayPop,
    ArrayLen,

    MapInsert,
    MapRemove,
    MapGet,
}

impl TryFrom<u16> for BuiltinField {
    type Error = ();

    fn try_from(value: u16) -> Result<Self, Self::Error> {
        if value as usize >= Self::VARIANT_COUNT {
            return Err(());
        }
        Ok(unsafe { std::mem::transmute::<u16, Self>(value) })
    }
}

impl Builtin {
    pub fn name(self) -> &'static str {
        match self {
            Self::Assert => "assert",
            Self::Println => "println",
            Self::ReadFile => "read_file",
            Self::Exit => "exit",
        }
    }
}

impl TryFrom<u16> for Builtin {
    type Error = u16;

    fn try_from(value: u16) -> Result<Self, Self::Error> {
        if value as usize >= Self::VARIANT_COUNT {
            return Err(value);
        }
        Ok(unsafe { std::mem::transmute::<u16, Self>(value) })
    }
}
