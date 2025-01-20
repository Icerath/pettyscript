use crate::bytecode::{OpCode, VERSION};

const NUM_BUILTINS: u32 = 1;

#[derive(Debug, Clone)]
pub enum Value {
    Null,
    Bool(bool),
    Int(i64),
    Builtin(Builtin),
    StringLiteral { ptr: u32, len: u32 },
    RangeInclusive(Box<[i64; 2]>),
}

#[derive(Debug, Clone, Copy)]
pub enum Builtin {
    Println,
}

pub fn execute_bytecode(bytecode: &[u8]) {
    const { assert!(size_of::<Value>() == 16) };

    let mut reader = BytecodeReader::new(bytecode);
    let version = reader.read_u32();
    assert_eq!(version, VERSION);
    let len_consts = reader.read_u32() as usize;
    reader.bytes = &reader.bytes[reader.head..];
    reader.head = 0;
    let consts = &reader.bytes[..len_consts];
    reader.bytes = &reader.bytes[len_consts..];

    let mut idents = vec![];

    let mut stack = vec![];

    macro_rules! pop_int {
        () => {
            match stack.pop().unwrap() {
                Value::Int(int) => int,
                val => panic!("{val:?}"),
            }
        };
    }

    while let Some(&byte) = reader.bytes.get(reader.head) {
        reader.head += 1;
        let op = OpCode::try_from(byte).unwrap();
        match op {
            OpCode::LoadConst => {
                match reader.read::<1>()[0] {
                    0 => stack.push(Value::Int(i64::from_le_bytes(*reader.read::<8>()))),
                    1 => {
                        let ptr = reader.read_u32();
                        let len = reader.read_u32();
                        stack.push(Value::StringLiteral { ptr, len });
                    }
                    n => unreachable!("{n:?}"),
                };
            }
            OpCode::RangeInclusive => {
                let Value::Int(end) = stack.pop().unwrap() else { unimplemented!() };
                let Value::Int(start) = stack.pop().unwrap() else { unimplemented!() };
                stack.push(Value::RangeInclusive(Box::new([start, end])));
            }
            OpCode::IterNext => {
                let last = stack.last_mut().unwrap();
                match last {
                    Value::RangeInclusive(range) => {
                        let [start, end] = **range;
                        if start <= end {
                            range[0] += 1;
                            stack.push(Value::Int(start));
                            stack.push(Value::Bool(true));
                        } else {
                            stack.push(Value::Bool(false));
                        }
                    }
                    _ => unimplemented!("{last:?}"),
                }
            }
            OpCode::CJump => {
                let Value::Bool(bool) = stack.pop().unwrap() else { unimplemented!() };
                let label = reader.read_u32();
                if !bool {
                    reader.head = label as usize;
                }
            }
            OpCode::FnCall => {
                let numargs = reader.read::<1>()[0];

                let function = stack.pop().unwrap();
                match function {
                    Value::Builtin(Builtin::Println) => {
                        assert_eq!(numargs, 1);
                        let value = stack.pop().unwrap();
                        match value {
                            Value::Null => println!("null"),
                            Value::Bool(bool) => println!("{bool}"),
                            Value::Builtin(function) => println!("Function::{function:?}"),
                            Value::Int(int) => println!("{int}"),
                            Value::RangeInclusive(range) => {
                                println!("{}..={}", &range[0], &range[1]);
                            }
                            Value::StringLiteral { ptr, len } => {
                                let str = std::str::from_utf8(
                                    &consts[ptr as usize..ptr as usize + len as usize],
                                )
                                .unwrap();
                                println!("{str}");
                            }
                        }
                    }
                    _ => todo!("{function:?}"),
                }
                for _ in 0..numargs {}

                stack.push(Value::Null);
            }
            OpCode::Pop => _ = stack.pop(),
            OpCode::Jump => {
                let to = reader.read_u32();
                reader.head = to as usize;
            }
            OpCode::Store => {
                let ident = reader.read_u32();
                let value = stack.pop().unwrap();

                idents.resize_with(idents.len().max(ident as usize + 1), || Value::Null);
                idents[ident as usize] = value;
            }
            OpCode::Load => {
                let ident = reader.read_u32();
                let is_builtin = ident < NUM_BUILTINS;
                let value = if is_builtin {
                    match ident {
                        0 => Value::Builtin(Builtin::Println),
                        _ => unreachable!(),
                    }
                } else {
                    idents[ident as usize].clone()
                };
                stack.push(value);
            }
            OpCode::Mod => {
                let rhs = pop_int!();
                let lhs = pop_int!();
                stack.push(Value::Int(lhs % rhs));
            }
            OpCode::Eq => {
                let rhs = pop_int!();
                let lhs = pop_int!();
                stack.push(Value::Bool(lhs == rhs));
            }
            _ => todo!("{op:?}"),
        }
    }
}

pub struct BytecodeReader<'a> {
    bytes: &'a [u8],
    head: usize,
}

impl<'a> BytecodeReader<'a> {
    pub fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, head: 0 }
    }

    pub fn read<const N: usize>(&mut self) -> &[u8; N] {
        let bytes = self.bytes[self.head..self.head + N].try_into().unwrap();
        self.head += N;
        bytes
    }

    pub fn read_u32(&mut self) -> u32 {
        u32::from_le_bytes(*self.read::<4>())
    }
}
