use enum_kinds::EnumKind;
use rustc_hash::FxHashMap;

pub const VERSION: u32 = 0;

#[derive(EnumKind, Clone, Copy, Debug)]
#[enum_kind(OpCode)]
pub enum Op {
    FnCall { numargs: u8 },
    Mod,
    Eq,
    Add,
    Range,
    RangeInclusive,
    LoadConst(ConstantKey),
    Jump(u32),
    CJump(u32),
    Load(u32),
    Store(u32),
    Pop,
    IterNext,
}

pub enum Constant {
    String(&'static str),
    Int(i64),
}

#[derive(Clone, Copy, Debug)]
pub enum ConstantKey {
    String { ptr: u32, len: u32 },
    Int(i64),
}

#[derive(Default)]
pub struct BytecodeBuilder {
    string_map: FxHashMap<&'static str, u32>,
    string_data: Vec<u8>,
    identifiers: FxHashMap<&'static str, u32>,
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
        println!("{instruction:?}");

        let op = OpCode::from(instruction);
        self.instruction_data.push(op as u8);

        match instruction {
            I::FnCall { numargs } => self.instruction_data.push(numargs),
            I::Store(ident) => self.instruction_data.extend(ident.to_le_bytes()),
            I::CJump(label) | I::Jump(label) => {
                self.jumps.push(self.instruction_data.len());
                self.instruction_data.extend(label.to_le_bytes());
            }
            I::LoadConst(key) => {
                let bytes: [u8; 16] = unsafe { std::mem::transmute(key) };
                self.instruction_data.extend(&bytes);
            }
            _ => {}
        }
    }

    pub fn insert_identifer(&mut self, ident: &'static str) -> u32 {
        let len = self.identifiers.len() as u32;
        *self.identifiers.entry(ident).or_insert(len)
    }

    pub fn insert_constant(&mut self, constant: Constant) -> ConstantKey {
        match constant {
            Constant::String(str) => {
                let ptr = *self.string_map.entry(str).or_insert_with(|| {
                    let ptr = self.string_data.len() as u32;
                    self.string_data.extend(str.as_bytes());
                    ptr
                });
                ConstantKey::String {
                    ptr,
                    len: str.len().try_into().expect("Tried to insert a string too large"),
                }
            }
            Constant::Int(int) => ConstantKey::Int(int),
        }
    }

    pub fn finish(mut self) -> Vec<u8> {
        for &jump in &self.jumps {
            let bytes: &mut [u8; 4] =
                (&mut self.instruction_data[jump..jump + 4]).try_into().unwrap();
            let label = u32::from_le_bytes(*bytes);
            let new_label = self.labels[label as usize];
            println!("replaced {label} with {new_label}");
            *bytes = new_label.to_le_bytes();
        }
        println!("{:?}", self.string_map);
        println!("{:?}", self.identifiers);
        let mut output = vec![];
        output.extend(VERSION.to_le_bytes());
        let string_data_len: u32 = self.string_data.len().try_into().unwrap();
        output.extend(string_data_len.to_le_bytes());
        output.extend_from_slice(&self.string_data);
        output.extend_from_slice(&self.instruction_data);
        output
    }
}
