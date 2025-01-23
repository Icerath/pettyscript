use core::fmt;
use std::{
    cell::RefCell,
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
    EnumVariant { name: StrIdent, key: u32 },
    Char(char),
    Int(i64),
    Builtin(Builtin),
    Function { label: u32 },
    StringLiteral { ptr: u32, len: u32 },
    String(Rc<Box<str>>),
    Range(Box<[i64; 2]>),
    RangeInclusive(Box<[i64; 2]>),
    Struct { fields: Rc<RefCell<FxHashMap<StrIdent, Value>>> },
}

#[derive(macros::NumVariants, Debug, Clone, Copy, PartialEq)]
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

    let mut idents = vec![FxHashMap::default()];
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
            OpCode::LoadChar => {
                let char = char::try_from(reader.read_u32()).unwrap();
                stack.push(Value::Char(char));
            }
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
                    Value::Range(range) => {
                        let [start, end] = **range;
                        if start < end {
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
                    Value::Builtin(builtin) => match builtin {
                        Builtin::Println => {
                            assert_eq!(numargs, 1);
                            let value = stack.pop().unwrap();
                            writeln!(stdout, "{}", DisplayValue { consts, value: &value })?;
                            stack.push(Value::Null);
                        }
                        Builtin::ReadFile => {
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
                        Builtin::StartsWith => {
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
                        Builtin::StrLen => {
                            assert_eq!(numargs, 1);
                            let len = match stack.pop().unwrap() {
                                Value::StringLiteral { len, .. } => len,
                                Value::String(ref str) => str.len() as u32,
                                val => panic!("{val:?}"),
                            };

                            stack.push(Value::Int(len as i64));
                        }
                        Builtin::Trim => {
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
                        Builtin::IsAlphabetical => 'block: {
                            assert_eq!(numargs, 1);
                            let value = stack.pop().unwrap();
                            let str = match value {
                                Value::StringLiteral { ptr, len } => {
                                    str_literal!(ptr, len).to_str().unwrap()
                                }
                                Value::String(ref str) => str,
                                Value::Char(char) => {
                                    stack.push(Value::Bool(char.is_alphabetic()));
                                    break 'block;
                                }
                                val => panic!("{val:?}"),
                            };
                            stack.push(Value::Bool(str.chars().all(|c| c.is_alphabetic())))
                        }
                        Builtin::IsDigit => 'block: {
                            assert_eq!(numargs, 1);
                            let value = stack.pop().unwrap();
                            let str = match value {
                                Value::StringLiteral { ptr, len } => {
                                    str_literal!(ptr, len).to_str().unwrap()
                                }
                                Value::String(ref str) => str,
                                Value::Char(char) => {
                                    stack.push(Value::Bool(char.is_ascii_digit()));
                                    break 'block;
                                }
                                val => panic!("{val:?}"),
                            };
                            stack.push(Value::Bool(str.chars().all(|c| c.is_ascii_digit())))
                        }
                        Builtin::Exit => {
                            assert!(numargs <= 1);
                            let int = if numargs == 1 { pop_int!() as i32 } else { 0 };
                            std::process::exit(int)
                        }
                    },

                    Value::Function { label } => {
                        let here = reader.head;
                        call_stack.push(here);
                        reader.head = label as usize;
                    }
                    _ => todo!("{function:?}"),
                }
            }
            OpCode::Pop => _ = stack.pop().unwrap(),
            OpCode::Dup => stack.push(stack.last().unwrap().clone()),
            OpCode::Jump => {
                let to = reader.read_u32();
                reader.head = to as usize;
            }
            OpCode::Store => {
                let ident = reader.read_ident();
                let scope = reader.read_u32() as usize;
                let value = stack.pop().unwrap();
                if scope >= idents.len() {
                    idents.resize_with(scope + 1, FxHashMap::default);
                }
                idents[scope].insert(ident, value);
            }
            OpCode::LoadBuiltin => {
                stack.push(Value::Builtin(Builtin::try_from(reader.read_u16()).unwrap()));
            }
            OpCode::Load => {
                let ident = reader.read_ident();
                let scope = reader.read_u32() as usize;
                let ident_str = str_literal!(ident.ptr, ident.len);
                let value = match idents[scope].get(&ident) {
                    Some(value) => value.clone(),
                    None => panic!("Unknown identifier: '{}'", ident_str.as_bstr()),
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
                        Value::String(rhs) => lhs == rhs,
                        _ => panic!(),
                    },
                    Value::Char(lhs) => match rhs {
                        Value::Null => false,
                        Value::Char(rhs) => lhs == rhs,
                        Value::StringLiteral { ptr, len } => {
                            str_char_eq(str_literal!(ptr, len), lhs)
                        }
                        Value::String(rhs) => str_char_eq(rhs.as_bytes(), lhs),
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
                fields.borrow_mut().insert(field, value);
            }
            OpCode::StoreEnumVariant => {
                let variant = reader.read_ident();
                let Value::Struct { fields } = stack.last_mut().unwrap() else { panic!() };
                fields.borrow_mut().insert(variant, Value::EnumVariant { name: variant, key: 0 });
            }
            OpCode::EmptyStruct => {
                stack.push(Value::Struct { fields: Rc::default() });
            }
            OpCode::LoadField => {
                let ident = reader.read_ident();
                let fields = match stack.pop().unwrap() {
                    Value::Struct { fields } => fields,
                    other => panic!("{other:?}"),
                };
                let value = match fields.borrow().get(&ident) {
                    Some(value) => value.clone(),
                    None => panic!(
                        "struct does not contain field: {:?}",
                        str_literal!(ident.ptr, ident.len).as_bstr()
                    ),
                };
                stack.push(value);
            }
            OpCode::Index => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
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
                    Value::StringLiteral { ptr, len } => {
                        let str = &str_literal!(ptr, len);
                        match rhs {
                            Value::Int(x) => Value::Char(str.chars().nth(x as usize).unwrap()),
                            Value::RangeInclusive(_) => todo!(),
                            Value::Range(range) => {
                                let range_start: u32 = range[0].try_into().unwrap();
                                let range_len: u32 = range[1].try_into().unwrap();
                                assert!(range_len > range_start);
                                assert!(range_start <= len);
                                assert!(range_len <= len);

                                Value::StringLiteral {
                                    ptr: ptr + range_start,
                                    len: range_len - range_start,
                                }
                            }
                            _ => panic!("{rhs:?}"),
                        }
                    }
                    _ => todo!("{lhs:?}"),
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

    debug_assert!(stack.is_empty(), "last: {:?}\nlen: {}", stack.last(), stack.len());

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
            Value::EnumVariant { name: StrIdent { ptr, len }, .. } => {
                write!(f, "{}", self.consts[*ptr as usize..*ptr as usize + *len as usize].as_bstr())
            }

            Value::Char(char) => write!(f, "{char}"),
            Value::Struct { fields } => {
                write!(f, "{{")?;
                for (i, (key, value)) in fields.borrow().iter().enumerate() {
                    let key = self.consts[key.ptr as usize..key.ptr as usize + key.len as usize]
                        .as_bstr();
                    let prefix = if i != 0 { "," } else { "" };
                    write!(f, "{prefix} {key}: {}", DisplayValue { value, ..*self })?;
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

    pub fn read_u16(&mut self) -> u16 {
        u16::from_le_bytes(*self.read::<2>())
    }
}
