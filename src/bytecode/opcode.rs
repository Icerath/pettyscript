use bstr::ByteSlice;
use rustc_hash::FxHashMap;

use crate::vm::Builtin;

pub const VERSION: u32 = 0;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct StrIdent {
    pub ptr: u32,
    pub len: u32,
}

#[derive(macros::EnumKind, Clone, Copy, Debug)]
#[enum_kind(OpCode)]
#[repr(u8)]
pub enum Op {
    Less,
    Greater,
    EmptyStruct,
    Ret,
    FnCall { numargs: u8 },
    Not,
    Mod,
    Eq,
    Add,
    Range,
    RangeInclusive,
    LoadNull,
    Index,
    StoreEnumVariant(StrIdent),
    CreateFunction { label: u32 },
    LoadTrue,
    LoadFalse,
    LoadChar(char),
    LoadInt(i64),
    LoadString { ptr: u32, len: u32 },
    Jump(u32),
    CJump(u32),
    Load(StrIdent, u32),
    Store(StrIdent, u32),
    LoadField(StrIdent),
    StoreField(StrIdent),
    LoadBuiltin(Builtin),
    Pop,
    Dup,
    IterNext,
    End,
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

    pub fn insert(&mut self, instruction: Op) {
        use Op as I;

        const { assert!(size_of::<Op>() == 16) };
        const { assert!(size_of::<OpCode>() == 1) };

        let op = OpCode::from(instruction);
        self.instruction_data.push(op as u8);

        match instruction {
            I::StoreEnumVariant(name) => {
                self.instruction_data.extend(name.ptr.to_le_bytes());
                self.instruction_data.extend(name.len.to_le_bytes());
            }
            I::FnCall { numargs } => self.instruction_data.push(numargs),
            I::Store(ident, scope) | I::Load(ident, scope) => {
                let StrIdent { ptr, len } = ident;
                self.instruction_data.extend(ptr.to_le_bytes());
                self.instruction_data.extend(len.to_le_bytes());
                self.instruction_data.extend(scope.to_le_bytes());
            }
            I::StoreField(field) | I::LoadField(field) => {
                let StrIdent { ptr, len } = field;
                self.instruction_data.extend(ptr.to_le_bytes());
                self.instruction_data.extend(len.to_le_bytes());
            }
            I::CreateFunction { label } | I::CJump(label) | I::Jump(label) => {
                self.jumps.push(self.instruction_data.len());
                self.instruction_data.extend(label.to_le_bytes());
            }
            I::LoadBuiltin(builtin) => self.instruction_data.extend((builtin as u16).to_le_bytes()),
            I::LoadChar(char) => self.instruction_data.extend((char as u32).to_le_bytes()),
            I::LoadInt(int) => self.instruction_data.extend(int.to_le_bytes()),
            I::LoadString { ptr, len } => {
                self.instruction_data.extend(ptr.to_le_bytes());
                self.instruction_data.extend(len.to_le_bytes());
            }
            _ => {}
        }
    }

    pub fn insert_identifer(&mut self, ident: &'static str) -> StrIdent {
        let [ptr, len] = self.insert_string(ident);
        StrIdent { ptr, len }
    }

    pub fn read_identifer(&self, ident: StrIdent) -> &str {
        let key = &self.string_data[ident.ptr as usize..ident.ptr as usize + ident.len as usize];
        let key = key.to_str().unwrap();
        self.string_map.get_key_value(key).unwrap().0
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
        let _ = Op::End;
        if value >= OpCode::End as u8 {
            return Err(());
        }
        unsafe { std::mem::transmute(value) }
    }
}
