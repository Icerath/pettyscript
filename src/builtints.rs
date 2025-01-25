#[derive(
    macros::NumVariants, macros::AllVariants, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord,
)]
#[repr(u16)]
pub enum Builtin {
    Println,
    ReadFile,
    StartsWith,
    StrLen,
    Trim,
    IsDigit,
    IsAlphabetical,
    Exit,
    ArrayPush,
    ArrayPop,
    CreateMap,
    InsertMap,
}

impl Builtin {
    pub fn name(self) -> &'static str {
        match self {
            Self::CreateMap => "create_map",
            Self::InsertMap => "insert_map",
            Self::ArrayPush => "array_push",
            Self::ArrayPop => "array_pop",
            Self::Println => "println",
            Self::ReadFile => "read_file",
            Self::StartsWith => "starts_with",
            Self::StrLen => "str_len",
            Self::Trim => "trim",
            Self::IsDigit => "is_digit",
            Self::IsAlphabetical => "is_alphabetical",
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
