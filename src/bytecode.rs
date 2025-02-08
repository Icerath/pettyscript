use macros::*;
use rustc_hash::FxHashMap;

use crate::builtints::{Builtin, MethodBuiltin};

pub const VERSION: u32 = 0;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct StrIdent {
    pub ptr: u32,
    pub len: u32,
}

#[derive(BcRead, BcWrite, EnumKind, NumVariants, Clone, Copy, Debug, PartialEq)]
#[enum_kind(OpCode)]
#[repr(u8)]
pub enum Instr {
    Abort,
    BuildFstr { num_segments: u16 },
    AddInt,
    CreateStruct { size: u32 },
    Ret,
    FnCall,
    Neg,
    Not,
    Mod,
    Eq,
    Greater,
    Less,
    Range,
    RangeInclusive,
    Index,
    LoadVariant(StrIdent),
    CreateFunction { stack_size: u16 },
    CreateMap,
    InsertMap,
    CreateArray { size: u16 },
    ArrayConcatStack,
    LoadBool(bool),
    LoadChar(char),
    LoadInt(i64),
    LoadIntSmall(i16),
    LoadString { ptr: u32, len: u32 },
    Jump(u32),
    CJump(u32),
    Load(u32),
    Store(u32),
    LoadGlobal(u32),
    CallBuiltinMethod(MethodBuiltin),
    LoadField(u32),
    StoreField(u32),
    Pop,
    Dup,
    IterRange,
    IterRangeInclusive,
}

trait BcRead: Sized {
    fn bc_read(bytes: &mut &[u8]) -> Self;
    unsafe fn bc_read_unchecked(bytes: &mut &[u8]) -> Self;
}

trait BcWrite {
    fn bc_write(&self, buf: &mut Vec<u8>);
}

macro_rules! impl_int {
    ($($int: ident),+) => {
        $(impl BcRead for $int {
            fn bc_read(bytes: &mut &[u8]) -> Self {
                let size = size_of::<Self>();
                let out = Self::from_le_bytes(bytes[0..size].try_into().unwrap());
                *bytes = &bytes[size..];
                out
            }

            unsafe fn bc_read_unchecked(bytes: &mut &[u8]) -> Self {
                let size = size_of::<Self>();
                let out = Self::from_le_bytes(bytes[0..size].try_into().unwrap());
                unsafe { *bytes = bytes.get_unchecked(size..) };
                out
            }
        }
        impl BcWrite for $int {
            fn bc_write(&self, bytes: &mut Vec<u8>) {
                bytes.extend(self.to_le_bytes());
            }
        })+
    };
}

macro_rules! impl_from {
    ($ty: ident, $int: ident) => {
        impl BcRead for $ty {
            fn bc_read(bytes: &mut &[u8]) -> Self {
                Self::try_from($int::bc_read(bytes)).unwrap()
            }

            unsafe fn bc_read_unchecked(bytes: &mut &[u8]) -> Self {
                unsafe { Self::try_from($int::bc_read_unchecked(bytes)).unwrap_unchecked() }
            }
        }
        impl BcWrite for $ty {
            fn bc_write(&self, bytes: &mut Vec<u8>) {
                (*self as $int).bc_write(bytes);
            }
        }
    };
}

impl_int!(u8, u16, u32, i16, i64);
impl_from!(char, u32);
impl_from!(Builtin, u16);
impl_from!(MethodBuiltin, u8);

impl BcRead for bool {
    fn bc_read(bytes: &mut &[u8]) -> Self {
        match u8::bc_read(bytes) {
            0 => false,
            1 => true,
            _ => panic!(),
        }
    }

    unsafe fn bc_read_unchecked(bytes: &mut &[u8]) -> Self {
        (unsafe { u8::bc_read_unchecked(bytes) } & 1) == 1
    }
}

impl BcWrite for bool {
    fn bc_write(&self, buf: &mut Vec<u8>) {
        u8::from(*self).bc_write(buf);
    }
}

impl BcRead for StrIdent {
    fn bc_read(bytes: &mut &[u8]) -> Self {
        Self { ptr: u32::bc_read(bytes), len: u32::bc_read(bytes) }
    }

    unsafe fn bc_read_unchecked(bytes: &mut &[u8]) -> Self {
        unsafe { Self { ptr: u32::bc_read_unchecked(bytes), len: u32::bc_read_unchecked(bytes) } }
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
    global_scope_size: u32,
    string_map: FxHashMap<&'static str, u32>,
    string_data: Vec<u8>,
    instruction_data: Vec<u8>,
    labels: Vec<u32>,
    jumps: Vec<usize>,
}

impl BytecodeBuilder {
    pub fn set_global_stack_size(&mut self, size: u32) {
        self.global_scope_size = size;
    }

    pub fn create_label(&mut self) -> u32 {
        let x = self.labels.len() as u32;
        self.labels.push(u32::MAX);
        x
    }

    pub fn insert_label(&mut self, label: u32) {
        self.labels.resize(self.labels.len().max(label as usize + 1), 0);
        self.labels[label as usize] = self.instruction_data.len() as u32;
    }

    pub fn insert(&mut self, instruction: Instr) {
        const { assert!(size_of::<Instr>() == 16) };
        const { assert!(size_of::<OpCode>() == 1) };

        self.instruction_data.push(OpCode::from(instruction) as u8);
        match instruction {
            Instr::CJump(_) | Instr::Jump(_) => self.jumps.push(self.instruction_data.len()),
            _ => {}
        }
        instruction.bc_write(&mut self.instruction_data);
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
        output.extend(self.global_scope_size.to_le_bytes());
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
        if value as usize >= Instr::VARIANT_COUNT {
            return Err(());
        }
        Ok(unsafe { std::mem::transmute::<u8, Self>(value) })
    }
}
