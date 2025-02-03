#[derive(
    macros::NumVariants, macros::AllVariants, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord,
)]
#[repr(u16)]
pub enum Builtin {
    Println,
    ReadFile,
    Exit,
    Assert,
    ParseInt,
}

#[derive(macros::NumVariants, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum MethodBuiltin {
    IntAbs,

    StrTrim,
    StrStartsWith,
    StrIsDigit,
    StrIsAlphabetic,
    StrLines,

    CharIsDigit,
    CharIsAlphabetic,

    MapGet,
    MapInsert,
    MapRemove,

    ArrayPush,
    ArrayPop,
    ArraySortInt,
}

impl TryFrom<u8> for MethodBuiltin {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value as usize >= Self::VARIANT_COUNT {
            return Err(());
        }
        Ok(unsafe { std::mem::transmute::<u8, Self>(value) })
    }
}

#[derive(macros::NumVariants, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
#[repr(u16)]
pub enum BuiltinField {
    StrLen,
    ArrayLen,
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
            Self::ParseInt => "parse_int",
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
