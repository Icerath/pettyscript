use macros::*;
use rustc_hash::FxHashMap;

use crate::builtints::Builtin;

pub const VERSION: u32 = 0;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StrIdent {
    pub ptr: u32,
    pub len: u32,
}

#[derive(BcRead, BcWrite, EnumKind, NumVariants, Clone, Copy, Debug, PartialEq)]
#[enum_kind(OpCode)]
#[repr(u8)]
pub enum Op {
    BuildFstr { num_segments: u16 },
    AddInt,
    EmptyStruct,
    Ret,
    FnCall { numargs: u8 },
    Neg,
    Not,
    Mod,
    Eq(EqTag),
    Greater(EqTag),
    Less(EqTag),
    Add,
    Range,
    RangeInclusive,
    LoadNull,
    Index,
    StoreEnumVariant(StrIdent),
    CreateFunction,
    CreateMap,
    InsertMap,
    CreateArray,
    ArrayPush,
    LoadTrue,
    LoadFalse,
    LoadChar(char),
    LoadInt(i64),
    LoadString { ptr: u32, len: u32 },
    Jump(u32),
    CJump(u32),
    Load(u32),
    Store(u32),
    SetStackSize(u16),
    LoadGlobal(u32),
    LoadField(StrIdent),
    StoreField(StrIdent),
    Pop,
    Dup,
    IterRange,
    IterRangeInclusive,
}

#[derive(macros::NumVariants, Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum EqTag {
    Int,
    Str,
    Char,
    Bool,
}

impl TryFrom<u8> for EqTag {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value as usize >= Self::VARIANT_COUNT {
            return Err(());
        }
        unsafe { std::mem::transmute(value) }
    }
}

trait BcRead: Sized {
    fn bc_read(bytes: &mut &[u8]) -> Self;
}
trait BcWrite {
    fn bc_write(&self, buf: &mut Vec<u8>);
}

macro_rules! impl_int {
    ($int: ident) => {
        impl BcRead for $int {
            fn bc_read(bytes: &mut &[u8]) -> Self {
                let size = size_of::<Self>();
                let out = Self::from_le_bytes(bytes[0..size].try_into().unwrap());
                *bytes = &bytes[size..];
                out
            }
        }
        impl BcWrite for $int {
            fn bc_write(&self, bytes: &mut Vec<u8>) {
                bytes.extend(self.to_le_bytes());
            }
        }
    };
}

macro_rules! impl_from {
    ($ty: ident, $int: ident) => {
        impl BcRead for $ty {
            fn bc_read(bytes: &mut &[u8]) -> Self {
                Self::try_from($int::bc_read(bytes)).unwrap()
            }
        }
        impl BcWrite for $ty {
            fn bc_write(&self, bytes: &mut Vec<u8>) {
                (*self as $int).bc_write(bytes);
            }
        }
    };
}

impl_int!(u8);
impl_int!(u16);
impl_int!(u32);
impl_int!(i64);
impl_from!(char, u32);
impl_from!(Builtin, u16);
impl_from!(EqTag, u8);

impl BcRead for StrIdent {
    fn bc_read(bytes: &mut &[u8]) -> Self {
        Self { ptr: u32::bc_read(bytes), len: u32::bc_read(bytes) }
    }
}

impl BcWrite for StrIdent {
    fn bc_write(&self, buf: &mut Vec<u8>) {
        self.ptr.bc_write(buf);
        self.len.bc_write(buf);
    }
}

#[derive(Default)]
pub struct BytecodeBuilder {
    string_map: FxHashMap<&'static str, u32>,
    string_data: Vec<u8>,
    instruction_data: Vec<u8>,
    labels: Vec<u32>,
    jumps: Vec<usize>,
}

impl BytecodeBuilder {
    pub fn create_label(&mut self) -> u32 {
        let x = self.labels.len() as u32;
        self.labels.push(u32::MAX);
        x
    }

    pub fn insert_label(&mut self, label: u32) {
        self.labels.resize(self.labels.len().max(label as usize + 1), 0);
        self.labels[label as usize] = self.instruction_data.len() as u32;
    }

    pub fn create_set_stack_size(&mut self) -> usize {
        let out = self.instruction_data.len() + 1;
        self.insert(Op::SetStackSize(0));
        out
    }

    pub fn insert_set_stack_size(&mut self, label: usize, value: u16) {
        self.instruction_data[label..label + 2].copy_from_slice(&value.to_le_bytes());
    }

    pub fn insert(&mut self, instruction: Op) {
        const { assert!(size_of::<Op>() == 16) };
        const { assert!(size_of::<OpCode>() == 1) };

        self.instruction_data.push(OpCode::from(instruction) as u8);
        match instruction {
            Op::CJump(_) | Op::Jump(_) => self.jumps.push(self.instruction_data.len()),
            _ => {}
        }
        instruction.bc_write(&mut self.instruction_data);
    }

    pub fn insert_identifer(&mut self, ident: &'static str) -> StrIdent {
        let [ptr, len] = self.insert_string(ident);
        StrIdent { ptr, len }
    }

    pub fn insert_string(&mut self, str: &'static str) -> [u32; 2] {
        let ptr = *self.string_map.entry(str).or_insert_with(|| {
            let ptr = self.string_data.len().try_into().expect("String data has grown too large");
            self.string_data.extend(str.as_bytes());
            ptr
        });
        [ptr, str.len() as u32]
    }

    pub fn finish(mut self) -> Vec<u8> {
        for &jump in &self.jumps {
            let bytes: &mut [u8; 4] =
                (&mut self.instruction_data[jump..jump + 4]).try_into().unwrap();
            let label = u32::from_le_bytes(*bytes);
            let new_label = self.labels[label as usize];
            *bytes = new_label.to_le_bytes();
        }
        let mut output = vec![];
        output.extend(VERSION.to_le_bytes());
        let string_data_len: u32 = self.string_data.len().try_into().unwrap();
        output.extend(string_data_len.to_le_bytes());
        output.extend_from_slice(&self.string_data);
        output.extend_from_slice(&self.instruction_data);
        output
    }
}

impl TryFrom<u8> for OpCode {
    type Error = ();

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        if value as usize >= Op::VARIANT_COUNT {
            return Err(());
        }
        Ok(unsafe { std::mem::transmute::<u8, Self>(value) })
    }
}
