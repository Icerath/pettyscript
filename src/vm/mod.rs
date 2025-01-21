use core::fmt;
use std::{
    io::{self, Write},
    rc::Rc,
};

use bstr::ByteSlice;
use rustc_hash::FxHashMap;

use crate::bytecode::{OpCode, StrIdent, VERSION};

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Null,
    Bool(bool),
    Char(char),
    Int(i64),
    Builtin(Builtin),
    Function { label: u32 },
    StringLiteral { ptr: u32, len: u32 },
    String(Rc<Box<str>>),
    Range(Box<[i64; 2]>),
    RangeInclusive(Box<[i64; 2]>),
    Struct { fields: Box<FxHashMap<StrIdent, Value>> },
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Builtin {
    Println,
    ReadFile,
    StartsWith,
    StrLen,
    Trim,
}

pub fn execute_bytecode(bytecode: &[u8]) {
    let stdout = std::io::stdout().lock();
    execute_bytecode_with(stdout, bytecode).unwrap();
}

pub fn execute_bytecode_with<W>(mut stdout: W, bytecode: &[u8]) -> io::Result<()>
where
    W: Write,
{
    const { assert!(size_of::<Option<Value>>() == 16) };

    let mut reader = BytecodeReader::new(bytecode);
    let version = reader.read_u32();
    assert_eq!(version, VERSION);
    let len_consts = reader.read_u32() as usize;
    reader.bytes = &reader.bytes[reader.head..];
    reader.head = 0;
    let consts = &reader.bytes[..len_consts];
    reader.bytes = &reader.bytes[len_consts..];

    let mut idents = FxHashMap::default();
    let mut stack = vec![];
    let mut call_stack = vec![];

    macro_rules! pop_int {
        () => {
            match stack.pop().unwrap() {
                Value::Int(int) => int,
                val => panic!("{val:?}"),
            }
        };
    }

    macro_rules! str_literal {
        ($ptr: expr, $len: expr) => {{
            let ptr = $ptr;
            &consts[ptr as usize..ptr as usize + $len as usize]
        }};
    }

    while let Some(&byte) = reader.bytes.get(reader.head) {
        reader.head += 1;
        let op = OpCode::try_from(byte).unwrap();
        match op {
            OpCode::LoadInt => stack.push(Value::Int(i64::from_le_bytes(*reader.read::<8>()))),
            OpCode::LoadString => {
                let ptr = reader.read_u32();
                let len = reader.read_u32();
                stack.push(Value::StringLiteral { ptr, len });
            }
            OpCode::Range => {
                let Value::Int(end) = stack.pop().unwrap() else { unimplemented!() };
                let Value::Int(start) = stack.pop().unwrap() else { unimplemented!() };
                stack.push(Value::Range(Box::new([start, end])));
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
                        writeln!(stdout, "{}", DisplayValue { consts, value: &value })?;
                        stack.push(Value::Null);
                    }
                    Value::Builtin(Builtin::ReadFile) => {
                        assert_eq!(numargs, 1);
                        let string = match stack.pop().unwrap() {
                            Value::StringLiteral { ptr, len } => {
                                let str = str_literal!(ptr, len).to_str().unwrap();
                                std::fs::read_to_string(str).unwrap()
                            }
                            Value::String(str) => std::fs::read_to_string(&**str).unwrap(),
                            val => panic!("{val:?}"),
                        };
                        stack.push(Value::String(Rc::new(string.into())));
                    }
                    Value::Builtin(Builtin::StartsWith) => {
                        assert_eq!(numargs, 2);
                        let rhs = stack.pop().unwrap();
                        let lhs = stack.pop().unwrap();

                        let rhs = match rhs {
                            Value::StringLiteral { ptr, len } => {
                                std::str::from_utf8(str_literal!(ptr, len)).unwrap()
                            }
                            Value::String(ref str) => str,
                            val => panic!("{val:?}"),
                        };

                        let lhs = match lhs {
                            Value::StringLiteral { ptr, len } => {
                                std::str::from_utf8(str_literal!(ptr, len)).unwrap()
                            }
                            Value::String(ref str) => str,
                            val => panic!("{val:?}"),
                        };
                        stack.push(Value::Bool(lhs.starts_with(rhs)));
                    }
                    Value::Builtin(Builtin::StrLen) => {
                        assert_eq!(numargs, 1);
                        let len = match stack.pop().unwrap() {
                            Value::StringLiteral { len, .. } => len,
                            Value::String(ref str) => str.len() as u32,
                            val => panic!("{val:?}"),
                        };

                        stack.push(Value::Int(len as i64));
                    }
                    Value::Builtin(Builtin::Trim) => {
                        assert_eq!(numargs, 1);
                        let value = stack.pop().unwrap();
                        let str = match value {
                            Value::StringLiteral { ptr, len } => {
                                str_literal!(ptr, len).to_str().unwrap()
                            }
                            Value::String(ref str) => str,
                            val => panic!("{val:?}"),
                        };
                        stack.push(Value::String(Rc::new(str.trim().into())));
                    }
                    Value::Function { label } => {
                        let here = reader.head;
                        call_stack.push(here);
                        reader.head = label as usize;
                    }
                    _ => todo!("{function:?}"),
                }
            }
            OpCode::Pop => _ = stack.pop(),
            OpCode::Dup => stack.push(stack.last().unwrap().clone()),
            OpCode::Jump => {
                let to = reader.read_u32();
                reader.head = to as usize;
            }
            OpCode::Store => {
                let ident = reader.read_ident();
                let value = stack.pop().unwrap();
                idents.insert(ident, value);
            }
            OpCode::Load => {
                let ident = reader.read_ident();
                let ident_str = str_literal!(ident.ptr, ident.len);
                let value = match ident_str {
                    b"println" => Value::Builtin(Builtin::Println),
                    b"read_file" => Value::Builtin(Builtin::ReadFile),
                    b"starts_with" => Value::Builtin(Builtin::StartsWith),
                    b"str_len" => Value::Builtin(Builtin::StrLen),
                    b"trim" => Value::Builtin(Builtin::Trim),
                    _ => match idents.get(&ident) {
                        Some(value) => value.clone(),
                        None => panic!("Unknown identifier: '{}'", ident_str.as_bstr()),
                    },
                };
                stack.push(value);
            }
            OpCode::Mod => {
                let rhs = pop_int!();
                let lhs = pop_int!();
                stack.push(Value::Int(lhs % rhs));
            }
            OpCode::Eq => {
                let rhs = stack.pop().unwrap();
                let is_eq = match stack.pop().unwrap() {
                    Value::Null => rhs == Value::Null,
                    Value::Bool(lhs) => match rhs {
                        Value::Null => false,
                        Value::Bool(rhs) => lhs == rhs,
                        _ => panic!(),
                    },
                    Value::Int(lhs) => match rhs {
                        Value::Null => false,
                        Value::Int(rhs) => lhs == rhs,
                        _ => panic!(),
                    },
                    Value::StringLiteral { ptr, len } => match rhs {
                        Value::Null => false,
                        Value::Char(rhs) => str_char_eq(str_literal!(ptr, len), rhs),
                        Value::StringLiteral { ptr: rhs_ptr, len: rhs_len } => {
                            ptr == rhs_ptr && len == rhs_len
                        }
                        Value::String(rhs) => {
                            let lhs = str_literal!(ptr, len);
                            lhs == rhs.as_bytes()
                        }
                        _ => panic!(),
                    },
                    Value::String(lhs) => match rhs {
                        Value::Null => false,
                        Value::Char(rhs) => str_char_eq(lhs.as_bytes(), rhs),
                        Value::StringLiteral { ptr, len } => {
                            let rhs = str_literal!(ptr, len);
                            lhs.as_bytes() == rhs
                        }
                        _ => panic!(),
                    },
                    Value::Char(lhs) => match rhs {
                        Value::Null => false,
                        Value::Char(rhs) => lhs == rhs,
                        Value::StringLiteral { ptr, len } => {
                            str_char_eq(str_literal!(ptr, len), lhs)
                        }
                        _ => panic!(),
                    },
                    val => todo!("{val:?}"),
                };
                stack.push(Value::Bool(is_eq));
            }
            OpCode::Add => {
                let rhs = pop_int!();
                let lhs = pop_int!();
                stack.push(Value::Int(lhs + rhs));
            }
            OpCode::LoadTrue => stack.push(Value::Bool(true)),
            OpCode::LoadFalse => stack.push(Value::Bool(false)),
            OpCode::CreateFunction => {
                let label = reader.read_u32();
                stack.push(Value::Function { label });
            }
            OpCode::LoadNull => stack.push(Value::Null),
            OpCode::Ret => reader.head = call_stack.pop().unwrap(),
            OpCode::StoreField => {
                let field = reader.read_ident();
                let value = stack.pop().unwrap();
                let Value::Struct { fields } = stack.last_mut().unwrap() else {
                    unimplemented!("{:?}", stack.last().unwrap())
                };
                fields.insert(field, value);
            }
            OpCode::EmptyStruct => {
                stack.push(Value::Struct { fields: Box::default() });
            }
            OpCode::LoadField => {
                let ident = reader.read_ident();
                let fields = match stack.pop().unwrap() {
                    Value::Struct { fields } => fields,
                    other => panic!("{other:?}"),
                };
                let value = match fields.get(&ident) {
                    Some(value) => value.clone(),
                    None => panic!("struct does not contain field: {ident:?}"),
                };
                stack.push(value);
            }
            OpCode::Index => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.last().unwrap();
                let value = match lhs {
                    Value::String(str) => match rhs {
                        Value::Int(x) => Value::Char(str.chars().nth(x as usize).unwrap()),
                        Value::RangeInclusive(_) => todo!(),
                        Value::Range(range) => {
                            let [start, end] = *range;
                            Value::String(Rc::new(str[start as usize..end as usize].into()))
                        }
                        _ => panic!("{rhs:?}"),
                    },
                    _ => todo!(),
                };
                stack.push(value);
            }
            OpCode::Not => {
                let bool = match stack.pop().unwrap() {
                    Value::Null => false,
                    Value::Bool(bool) => bool,
                    _ => panic!(),
                };
                stack.push(Value::Bool(!bool));
            }
            OpCode::Less => {
                let rhs = stack.pop().unwrap();
                let is_less = match stack.pop().unwrap() {
                    Value::Int(lhs) => match rhs {
                        Value::Int(rhs) => lhs < rhs,
                        _ => panic!(),
                    },
                    val => todo!("{val:?}"),
                };
                stack.push(Value::Bool(is_less));
            }
            OpCode::Greater => {
                let rhs = stack.pop().unwrap();
                let is_greater = match stack.pop().unwrap() {
                    Value::Int(lhs) => match rhs {
                        Value::Int(rhs) => lhs > rhs,
                        _ => panic!(),
                    },
                    val => todo!("{val:?}"),
                };
                stack.push(Value::Bool(is_greater));
            }
            _ => todo!("{op:?}"),
        }
    }

    debug_assert!(stack.is_empty(), "{stack:?}");
    Ok(())
}

fn str_char_eq(str: &[u8], char: char) -> bool {
    str.len() == char.len_utf8() && str.chars().next().unwrap() == char
}

#[derive(Clone, Copy)]
struct DisplayValue<'a, 'b> {
    consts: &'a [u8],
    value: &'b Value,
}

impl fmt::Display for DisplayValue<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            Value::Char(char) => write!(f, "{char}"),
            Value::Struct { fields } => {
                write!(f, "{{")?;
                for (i, (key, value)) in fields.iter().enumerate() {
                    let key = self.consts[key.ptr as usize..key.ptr as usize + key.len as usize]
                        .as_bstr();
                    let prefix = if i != 0 { "," } else { "" };
                    write!(f, "{prefix} {key}: {}", Self { value, ..*self })?;
                }
                write!(f, " }}")
            }
            Value::Function { label } => write!(f, "Function at {label}"),
            Value::Null => write!(f, "null"),
            Value::Bool(bool) => write!(f, "{bool}"),
            Value::Builtin(function) => write!(f, "Function::{function:?}"),
            Value::Int(int) => write!(f, "{int}"),
            Value::Range(range) => write!(f, "{}..{}", &range[0], &range[1]),
            Value::RangeInclusive(range) => {
                write!(f, "{}..={}", &range[0], &range[1])
            }
            Value::StringLiteral { ptr, len } => {
                let ptr = *ptr as usize;
                let len = *len as usize;
                let str = std::str::from_utf8(&self.consts[ptr..ptr + len]).unwrap();
                write!(f, "{str}")
            }
            Value::String(str) => write!(f, "{str}"),
        }
    }
}

pub struct BytecodeReader<'a> {
    bytes: &'a [u8],
    head: usize,
}

impl<'a> BytecodeReader<'a> {
    pub fn read_ident(&mut self) -> StrIdent {
        let ptr = self.read_u32();
        let len = self.read_u32();
        StrIdent { ptr, len }
    }
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
