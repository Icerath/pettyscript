use core::fmt;
use std::{
    cell::{Cell, RefCell},
    collections::BTreeMap,
    io::{self, Write},
    rc::Rc,
};

use bstr::ByteSlice;

use crate::{
    builtints::{Builtin, MethodBuiltin},
    bytecode::{Op, StrIdent, VERSION},
};

pub type PettyMap = BTreeMap<Value, Value>;

// TODO: Remove Rc<Refcell> with indexes
// TODO: Replace BTreeMap with HashMap
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Value {
    Null,
    Bool(bool),
    EnumVariant { name: StrIdent, key: u32 },
    Char(char),
    Int(i64),
    Builtin(Builtin),
    MethodBuiltin(MethodBuiltin),
    Function { label: u32 },
    String(PettyStr),
    Array(Rc<RefCell<Vec<Value>>>),
    Map(Rc<RefCell<PettyMap>>),
    Range(Rc<[Cell<i64>; 2]>),
    RangeInclusive(Rc<[Cell<i64>; 2]>),
    Struct { fields: Rc<RefCell<BTreeMap<StrIdent, Value>>> },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PettyStr {
    Literal { ptr: u32, len: u32 },
    String(Rc<Box<str>>),
}

pub fn execute_bytecode(bytecode: &[u8]) {
    let stdout = std::io::stdout().lock();
    execute_bytecode_with(stdout, bytecode).unwrap();
}

pub fn execute_bytecode_with<W>(mut stdout: W, bytecode: &[u8]) -> io::Result<()>
where
    W: Write,
{
    // TODO: Fix Value Size
    // const { assert!(size_of::<Option<Value>>() == 16) };

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
    let mut variable_stacks: Vec<Vec<Value>> = vec![vec![]];
    variable_stacks[0].extend(Builtin::ALL.map(Value::Builtin));

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

    while reader.head < reader.bytes.len() {
        let op = Op::bc_read(&reader.bytes[reader.head..]);
        reader.head += 1 + op.size();
        match op {
            Op::ArrayPush => {
                let value = stack.pop().unwrap();
                let arr = stack.last_mut().unwrap();
                let Value::Array(arr) = arr else { panic!() };
                arr.borrow_mut().push(value);
            }
            Op::CreateArray => stack.push(Value::Array(Rc::default())),
            Op::LoadGlobal(offset) => stack.push(variable_stacks[0][offset as usize].clone()),
            Op::Load(offset) => {
                stack.push(variable_stacks.last().unwrap()[offset as usize].clone())
            }
            Op::Store(offset) => {
                let offset = offset as usize;
                let variable_stack = variable_stacks.last_mut().unwrap();
                if offset >= variable_stack.len() {
                    variable_stack.resize_with(offset + 1, || Value::Null);
                }
                variable_stack[offset] = stack.pop().unwrap()
            }
            Op::LoadChar(char) => stack.push(Value::Char(char)),
            Op::LoadInt(int) => stack.push(Value::Int(int)),
            Op::LoadString { ptr, len } => {
                stack.push(Value::String(PettyStr::Literal { ptr, len }))
            }
            Op::Range => {
                let Value::Int(end) = stack.pop().unwrap() else { unimplemented!() };
                let Value::Int(start) = stack.pop().unwrap() else { unimplemented!() };
                stack.push(Value::Range(Rc::new([Cell::new(start), Cell::new(end)])));
            }
            Op::RangeInclusive => {
                let Value::Int(end) = stack.pop().unwrap() else { unimplemented!() };
                let Value::Int(start) = stack.pop().unwrap() else { unimplemented!() };
                stack.push(Value::RangeInclusive(Rc::new([Cell::new(start), Cell::new(end)])));
            }
            Op::IterNext => {
                let last = stack.last().unwrap();
                match last {
                    Value::RangeInclusive(range) => {
                        let [start, end] = &*range.clone();
                        if start.get() <= end.get() {
                            stack.push(Value::Int(start.get()));
                            stack.push(Value::Bool(true));
                            start.set(start.get() + 1);
                        } else {
                            stack.push(Value::Bool(false));
                        }
                    }
                    Value::Range(range) => {
                        let [start, end] = &*range.clone();
                        if start.get() < end.get() {
                            stack.push(Value::Int(start.get()));
                            stack.push(Value::Bool(true));
                            start.set(start.get() + 1);
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
            Op::FnCall { numargs } => 'fn_call: {
                let function = stack.pop().unwrap();
                let value = match function {
                    Value::Builtin(builtin) => match builtin {
                        Builtin::CreateMap => Value::Map(Rc::default()),
                        Builtin::ArrayPush => {
                            assert_eq!(numargs, 2);
                            let value = stack.pop().unwrap();
                            let Value::Array(arr) = stack.pop().unwrap() else { panic!() };
                            arr.borrow_mut().push(value);
                            Value::Null
                        }
                        Builtin::ArrayPop => {
                            assert_eq!(numargs, 1);
                            let Value::Array(arr) = stack.pop().unwrap() else { panic!() };
                            let Some(value) = arr.borrow_mut().pop() else {
                                panic!("Tried to pop from empty array");
                            };
                            value
                        }
                        Builtin::Println => {
                            assert_eq!(numargs, 1);
                            let value = stack.pop().unwrap();
                            writeln!(stdout, "{}", DisplayValue { consts, value: &value })?;
                            Value::Null
                        }
                        Builtin::ReadFile => {
                            assert_eq!(numargs, 1);
                            let Value::String(str) = stack.pop().unwrap() else { panic!() };
                            let string = match str {
                                PettyStr::Literal { ptr, len } => {
                                    let str = str_literal!(ptr, len).to_str().unwrap();
                                    std::fs::read_to_string(str).unwrap()
                                }
                                PettyStr::String(str) => std::fs::read_to_string(&**str).unwrap(),
                            };
                            Value::String(PettyStr::String(Rc::new(string.into())))
                        }
                        Builtin::Exit => {
                            assert!(numargs <= 1);
                            let int = if numargs == 1 { pop_int!() as i32 } else { 0 };
                            std::process::exit(int)
                        }
                    },

                    Value::Function { label } => {
                        variable_stacks.push(vec![]);
                        let here = reader.head;
                        call_stack.push(here);
                        reader.head = label as usize;
                        break 'fn_call;
                    }
                    Value::MethodBuiltin(method) => match method {
                        MethodBuiltin::CharIsAlphabetic(char) => Value::Bool(char.is_alphabetic()),
                        MethodBuiltin::CharIsDigit(char) => Value::Bool(char.is_ascii_digit()),
                        MethodBuiltin::StrTrim { trimmed } => {
                            Value::String(PettyStr::String(trimmed))
                        }
                        MethodBuiltin::StrIsAlphabetic(str) => {
                            let str = match &str {
                                PettyStr::String(str) => str.as_bytes(),
                                PettyStr::Literal { ptr, len } => str_literal!(*ptr, *len),
                            };
                            Value::Bool(str.iter().all(|c| c.is_ascii_alphabetic()))
                        }
                        MethodBuiltin::StrIsDigit(str) => {
                            let str = match &str {
                                PettyStr::String(str) => str.as_bytes(),
                                PettyStr::Literal { ptr, len } => str_literal!(*ptr, *len),
                            };
                            Value::Bool(str.iter().all(|c| c.is_ascii_digit()))
                        }
                        MethodBuiltin::StrStartsWith(str) => {
                            assert_eq!(numargs, 1);
                            let Value::String(arg) = stack.pop().unwrap() else { panic!() };
                            let arg = match &arg {
                                PettyStr::String(str) => str.as_bytes(),
                                PettyStr::Literal { ptr, len } => str_literal!(*ptr, *len),
                            };
                            let str = match &str {
                                PettyStr::String(str) => str.as_bytes(),
                                PettyStr::Literal { ptr, len } => str_literal!(*ptr, *len),
                            };
                            Value::Bool(str.starts_with(arg))
                        }
                        MethodBuiltin::MapGet(map) => {
                            assert_eq!(numargs, 1);
                            let key = stack.pop().unwrap();
                            // TODO: Is this the right output for unknown key?
                            map.borrow().get(&key).cloned().unwrap_or(Value::Null)
                        }
                        MethodBuiltin::MapInsert(map) => {
                            assert_eq!(numargs, 2);
                            let value = stack.pop().unwrap();
                            let key = stack.pop().unwrap();
                            map.borrow_mut().insert(key, value);
                            Value::Null
                        }
                        MethodBuiltin::MapRemove(map) => {
                            assert_eq!(numargs, 1);
                            let key = stack.pop().unwrap();
                            map.borrow_mut().remove(&key);
                            Value::Null
                        }
                    },
                    _ => todo!(),
                };
                stack.push(value);
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
                    Value::String(PettyStr::Literal { ptr, len }) => match rhs {
                        Value::Null => false,
                        Value::Char(rhs) => str_char_eq(str_literal!(ptr, len), rhs),
                        Value::String(PettyStr::Literal { ptr: rhs_ptr, len: rhs_len }) => {
                            ptr == rhs_ptr && len == rhs_len
                        }
                        Value::String(PettyStr::String(rhs)) => {
                            let lhs = str_literal!(ptr, len);
                            lhs == rhs.as_bytes()
                        }
                        _ => panic!(),
                    },
                    Value::String(PettyStr::String(lhs)) => match rhs {
                        Value::Null => false,
                        Value::Char(rhs) => str_char_eq(lhs.as_bytes(), rhs),
                        Value::String(PettyStr::Literal { ptr, len }) => {
                            let rhs = str_literal!(ptr, len);
                            lhs.as_bytes() == rhs
                        }
                        Value::String(PettyStr::String(rhs)) => lhs == rhs,
                        _ => panic!(),
                    },
                    Value::Char(lhs) => match rhs {
                        Value::Null => false,
                        Value::Char(rhs) => lhs == rhs,
                        Value::String(PettyStr::Literal { ptr, len }) => {
                            str_char_eq(str_literal!(ptr, len), lhs)
                        }
                        Value::String(PettyStr::String(rhs)) => str_char_eq(rhs.as_bytes(), lhs),
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
            Op::CreateFunction => stack.push(Value::Function { label: reader.head as u32 + 5 + 5 }),
            Op::LoadNull => stack.push(Value::Null),
            Op::Ret => {
                reader.head = call_stack.pop().unwrap();
                variable_stacks.pop().unwrap();
            }
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
                let value = match stack.pop().unwrap() {
                    Value::Struct { fields } => match fields.borrow().get(&field) {
                        Some(value) => value.clone(),
                        None => panic!(
                            "struct does not contain field: {:?}",
                            str_literal!(field.ptr, field.len).as_bstr()
                        ),
                    },
                    Value::String(str) => load_str_field(consts, str, field),
                    Value::Char(char) => load_char_field(consts, char, field),
                    Value::Map(map) => load_map_field(consts, map, field),
                    other => panic!("{other:?}"),
                };
                stack.push(value);
            }
            Op::Index => {
                let rhs = stack.pop().unwrap();
                let lhs = stack.pop().unwrap();
                let value = match lhs {
                    Value::String(PettyStr::String(str)) => match rhs {
                        Value::Int(x) => Value::Char(str.chars().nth(x as usize).unwrap()),
                        Value::RangeInclusive(_) => todo!(),
                        Value::Range(range) => {
                            let [start, end] = &*range;
                            Value::String(PettyStr::String(Rc::new(
                                str[start.get() as usize..end.get() as usize].into(),
                            )))
                        }
                        _ => panic!("{rhs:?}"),
                    },
                    Value::String(PettyStr::Literal { ptr, len }) => {
                        let str = &str_literal!(ptr, len);
                        match rhs {
                            Value::Int(x) => Value::Char(str.chars().nth(x as usize).unwrap()),
                            Value::RangeInclusive(_) => todo!(),
                            Value::Range(range) => {
                                let range_start: u32 = range[0].get().try_into().unwrap();
                                let range_len: u32 = range[1].get().try_into().unwrap();
                                let new = &str[range_start as usize..range_len as usize];
                                let ptr_diff = new.as_ptr().addr() - str.as_ptr().addr();
                                Value::String(PettyStr::Literal {
                                    ptr: ptr + ptr_diff as u32,
                                    len: new.len() as u32,
                                })
                            }
                            _ => panic!("{rhs:?}"),
                        }
                    }
                    Value::Array(arr) => {
                        let Value::Int(rhs) = rhs else { panic!() };
                        arr.borrow()[rhs as usize].clone()
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
            Op::Neg => {
                let int = pop_int!();
                stack.push(Value::Int(-int));
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

    debug_assert!(stack.is_empty(), "last: {:?}\nlen: {}", stack.last(), stack.len());

    Ok(())
}

fn load_map_field(consts: &[u8], map: Rc<RefCell<PettyMap>>, field: StrIdent) -> Value {
    let field = &consts[field.ptr as usize..field.ptr as usize + field.len as usize];
    Value::MethodBuiltin(match field {
        b"get" => MethodBuiltin::MapGet(map),
        b"insert" => MethodBuiltin::MapInsert(map),
        b"remove" => MethodBuiltin::MapRemove(map),
        _ => panic!("map does not contain field: {}", field.as_bstr()),
    })
}

fn load_char_field(consts: &[u8], char: char, field: StrIdent) -> Value {
    let field = &consts[field.ptr as usize..field.ptr as usize + field.len as usize];
    Value::MethodBuiltin(match field {
        b"is_digit" => MethodBuiltin::CharIsDigit(char),
        b"is_alphabetic" => MethodBuiltin::CharIsAlphabetic(char),
        _ => panic!("char does not contain field: {}", field.as_bstr()),
    })
}

fn load_str_field(consts: &[u8], string: PettyStr, field: StrIdent) -> Value {
    let field = &consts[field.ptr as usize..field.ptr as usize + field.len as usize];
    let str = match &string {
        PettyStr::Literal { ptr, len } => &consts[*ptr as usize..*ptr as usize + *len as usize],
        PettyStr::String(str) => str.as_bytes(),
    };
    Value::MethodBuiltin(match (field, string.clone()) {
        (b"len", _) => return Value::Int(str.len() as i64),
        (b"trim", _) => {
            let trimmed = Rc::new(std::str::from_utf8(str).unwrap().trim().into());
            MethodBuiltin::StrTrim { trimmed }
        }
        (b"starts_with", str) => MethodBuiltin::StrStartsWith(str),
        (b"is_digit", str) => MethodBuiltin::StrIsDigit(str),
        (b"is_alphabetic", str) => MethodBuiltin::StrIsAlphabetic(str),
        _ => panic!("str does not contain field: {}", field.as_bstr()),
    })
}

fn str_char_eq(str: &[u8], char: char) -> bool {
    str.len() == char.len_utf8() && str.chars().next().unwrap() == char
}

#[derive(Clone, Copy)]
struct DisplayValue<'a, 'b> {
    consts: &'a [u8],
    value: &'b Value,
}

impl fmt::Debug for DisplayValue<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for DisplayValue<'_, '_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.value {
            Value::Map(map) => {
                let mut debug_map = f.debug_map();

                for (key, value) in &*map.borrow() {
                    debug_map.entry(
                        &DisplayValue { value: key, ..*self },
                        &DisplayValue { value, ..*self },
                    );
                }

                debug_map.finish()
            }
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
            Value::MethodBuiltin(method) => write!(f, "method: {method:?}"),
            Value::Int(int) => write!(f, "{int}"),
            Value::Range(range) => write!(f, "{}..{}", range[0].get(), range[1].get()),
            Value::RangeInclusive(range) => {
                write!(f, "{}..={}", range[0].get(), range[1].get())
            }
            Value::String(PettyStr::Literal { ptr, len }) => {
                let ptr = *ptr as usize;
                let len = *len as usize;
                let str = std::str::from_utf8(&self.consts[ptr..ptr + len]).unwrap();
                write!(f, "{str}")
            }
            Value::String(PettyStr::String(str)) => write!(f, "{str}"),
            Value::Array(values) => {
                let mut debug_list = f.debug_list();
                for value in &*values.borrow() {
                    debug_list.entry(&format_args!("{}", DisplayValue { value, ..*self }));
                }
                debug_list.finish()
            }
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
