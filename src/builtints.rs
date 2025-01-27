use std::rc::Rc;

use crate::vm::PettyStr;

#[derive(
    macros::NumVariants, macros::AllVariants, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord,
)]
#[repr(u16)]
pub enum Builtin {
    Println,
    ReadFile,
    Exit,
    ArrayPush,
    ArrayPop,
    CreateMap,
    InsertMap,
    GetMap,
    RemoveMap,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum MethodBuiltin {
    StrTrim { trimmed: Rc<Box<str>> },
    StrStartsWith(PettyStr),
    StrIsDigit(PettyStr),
    StrIsAlphabetic(PettyStr),
    CharIsDigit(char),
    CharIsAlphabetic(char),
}

impl Builtin {
    pub fn name(self) -> &'static str {
        match self {
            Self::CreateMap => "create_map",
            Self::InsertMap => "insert_map",
            Self::GetMap => "get_map",
            Self::RemoveMap => "remove_map",
            Self::ArrayPush => "array_push",
            Self::ArrayPop => "array_pop",
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
