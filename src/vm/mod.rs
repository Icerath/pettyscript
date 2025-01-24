use core::fmt;
use std::{
    cell::RefCell,
    io::{self, Write},
    rc::Rc,
};

use bstr::ByteSlice;
use rustc_hash::FxHashMap;

use crate::bytecode::{Op, StrIdent, VERSION};

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

#[derive(macros::NumVariants, macros::AllVariants, Debug, Clone, Copy, PartialEq)]
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

impl Builtin {
    pub fn name(self) -> &'static str {
        match self {
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
    let version = u32::from_le_bytes(*reader.read::<4>());
    assert_eq!(version, VERSION);
    let len_consts = u32::from_le_bytes(*reader.read::<4>()) as usize;
    reader.bytes = &reader.bytes[reader.head..];
    reader.head = 0;
    let consts = &reader.bytes[..len_consts];
    reader.bytes = &reader.bytes[len_consts..];

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

    const STACK_SIZE: usize = 8 * 1024 * 1024 / size_of::<Value>();

    let mut variable_stack = vec![Value::Null; STACK_SIZE];
    let mut stack_ptr = 0usize;

    for (offset, builtin) in Builtin::ALL.into_iter().enumerate() {
        variable_stack[stack_ptr + offset] = Value::Builtin(builtin);
    }

    while reader.head < reader.bytes.len() {
        let op = Op::bc_read(&reader.bytes[reader.head..]);
        reader.head += 1 + op.size();
        match op {
            Op::LoadGlobal(offset) => {
                let val = variable_stack[offset as usize].clone();
                stack.push(val);
            }
            Op::Load(offset) => {
                let val = variable_stack[stack_ptr + offset as usize].clone();
                stack.push(val);
            }
            Op::Store(offset) => {
                let val = stack.pop().unwrap();
                variable_stack[stack_ptr + offset as usize] = val;
            }
            Op::AddStackPtr(offset) => stack_ptr += offset as usize,
            Op::SubStackPtr(offset) => stack_ptr -= offset as usize,
            Op::LoadChar(char) => stack.push(Value::Char(char)),
            Op::LoadInt(int) => stack.push(Value::Int(int)),
            Op::LoadString { ptr, len } => stack.push(Value::StringLiteral { ptr, len }),
            Op::Range => {
                let Value::Int(end) = stack.pop().unwrap() else { unimplemented!() };
                let Value::Int(start) = stack.pop().unwrap() else { unimplemented!() };
                stack.push(Value::Range(Box::new([start, end])));
            }
            Op::RangeInclusive => {
                let Value::Int(end) = stack.pop().unwrap() else { unimplemented!() };
                let Value::Int(start) = stack.pop().unwrap() else { unimplemented!() };
                stack.push(Value::RangeInclusive(Box::new([start, end])));
            }
            Op::IterNext => {
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
            Op::CJump(label) => {
                let Value::Bool(bool) = stack.pop().unwrap() else { unimplemented!() };
                if !bool {
                    reader.head = label as usize;
                }
            }
            Op::FnCall { numargs } => {
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
                            let value = match value {
                                Value::StringLiteral { ptr, len } => {
                                    let str = str_literal!(ptr, len).to_str().unwrap();
                                    let new = str.trim();
                                    let ptr_diff = new.as_ptr().addr() - str.as_ptr().addr();
                                    Value::StringLiteral {
                                        ptr: ptr + ptr_diff as u32,
                                        len: new.len() as u32,
                                    }
                                }
                                Value::String(ref str) => Value::String(Rc::new(str.trim().into())),
                                val => panic!("{val:?}"),
                            };
                            stack.push(value);
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
                    _ => {}
                }
            }
            Op::Pop => _ = stack.pop().unwrap(),
            Op::Dup => stack.push(stack.last().unwrap().clone()),
            Op::Jump(label) => reader.head = label as usize,
            Op::Mod => {
                let rhs = pop_int!();
                let lhs = pop_int!();
                stack.push(Value::Int(lhs % rhs));
            }
            Op::Eq => {
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
            Op::Add => {
                let rhs = pop_int!();
                let lhs = pop_int!();
                stack.push(Value::Int(lhs + rhs));
            }
            Op::LoadTrue => stack.push(Value::Bool(true)),
            Op::LoadFalse => stack.push(Value::Bool(false)),
            Op::CreateFunction { label } => stack.push(Value::Function { label }),
            Op::LoadNull => stack.push(Value::Null),
            Op::Ret => reader.head = call_stack.pop().unwrap(),
            Op::StoreField(field) => {
                let value = stack.pop().unwrap();
                let Value::Struct { fields } = stack.last_mut().unwrap() else {
                    unimplemented!("{:?}", stack.last().unwrap())
                };
                fields.borrow_mut().insert(field, value);
            }
            Op::StoreEnumVariant(variant) => {
                let Value::Struct { fields } = stack.last_mut().unwrap() else { panic!() };
                fields.borrow_mut().insert(variant, Value::EnumVariant { name: variant, key: 0 });
            }
            Op::EmptyStruct => stack.push(Value::Struct { fields: Rc::default() }),
            Op::LoadField(field) => {
                let fields = match stack.pop().unwrap() {
                    Value::Struct { fields } => fields,
                    other => panic!("{other:?}"),
                };
                let value = match fields.borrow().get(&field) {
                    Some(value) => value.clone(),
                    None => panic!(
                        "struct does not contain field: {:?}",
                        str_literal!(field.ptr, field.len).as_bstr()
                    ),
                };
                stack.push(value);
            }
            Op::Index => {
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
                                let new = &str[range_start as usize..range_len as usize];
                                let ptr_diff = new.as_ptr().addr() - str.as_ptr().addr();
                                Value::StringLiteral {
                                    ptr: ptr + ptr_diff as u32,
                                    len: new.len() as u32,
                                }
                            }
                            _ => panic!("{rhs:?}"),
                        }
                    }
                    _ => todo!("{lhs:?}"),
                };
                stack.push(value);
            }
            Op::Not => {
                let bool = match stack.pop().unwrap() {
                    Value::Null => false,
                    Value::Bool(bool) => bool,
                    _ => panic!(),
                };
                stack.push(Value::Bool(!bool));
            }
            Op::Less => {
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
            Op::Greater => {
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
        }
    }

    // debug_assert!(stack.is_empty(), "last: {:?}\nlen: {}", stack.last(), stack.len());

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
    pub bytes: &'a [u8],
    pub head: usize,
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
}
