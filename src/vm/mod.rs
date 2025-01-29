#![expect(unsafe_op_in_unsafe_fn, reason = "I'm lazy")]

use core::fmt;
use std::{
    cell::{Cell, RefCell},
    collections::BTreeMap,
    fmt::Write as _,
    hint::{assert_unchecked, unreachable_unchecked},
    io::{self, Write},
    rc::Rc,
};

use crate::{
    builtints::{Builtin, MethodBuiltin},
    bytecode::{EqTag, Op, StrIdent, VERSION},
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
    Callable(Callable),
    String(PettyStr),
    Array(Rc<RefCell<Vec<Value>>>),
    Map(Rc<RefCell<PettyMap>>),
    Range(Rc<[Cell<i64>; 2]>),
    RangeInclusive(Rc<[Cell<i64>; 2]>),
    Struct { fields: Rc<RefCell<BTreeMap<StrIdent, Value>>> },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Callable {
    Builtin(Builtin),
    MethodBuiltin(MethodBuiltin),
    Function { label: u32 },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum PettyStr {
    Literal { ptr: u32, len: u32 },
    String(Rc<Box<str>>),
}

impl PettyStr {
    fn as_str<'a>(&'a self, consts: &'a str) -> &'a str {
        match *self {
            Self::Literal { ptr, len } => &consts[ptr as usize..ptr as usize + len as usize],
            Self::String(ref str) => str,
        }
    }
}

/// # Safety
/// bytecode must have been generated using codegen
pub unsafe fn execute_bytecode(bytecode: &[u8]) {
    let stdout = std::io::stdout().lock();
    unsafe { execute_bytecode_with(stdout, bytecode).unwrap() }
}

/// # Safety
/// bytecode must have been generated using codegen
pub unsafe fn execute_bytecode_with<W: Write>(stdout: W, bytecode: &[u8]) -> io::Result<()> {
    unsafe { VirtualMachine::new(bytecode, stdout).execute() }
}

struct VirtualMachine<'a, W> {
    consts: &'a str,
    instructions: &'a [u8],
    head: usize,
    stack: Vec<Value>,
    call_stack: Vec<usize>,
    variable_stacks: Vec<Vec<Value>>,
    stdout: W,
}

macro_rules! impl_pop_helper {
    ($name: ident, $variant: ident, $typ: ty) => {
        unsafe fn $name(&mut self) -> $typ {
            match self.pop_stack() {
                Value::$variant(inner) => inner,
                _ => unreachable_unchecked(),
            }
        }
    };
}

impl<'a, W: Write> VirtualMachine<'a, W> {
    impl_pop_helper! { pop_int, Int, i64 }

    impl_pop_helper! { pop_bool, Bool, bool }

    impl_pop_helper! { pop_str, String, PettyStr }

    unsafe fn pop_stack(&mut self) -> Value {
        Self::partial_pop_stack(&mut self.stack)
    }

    unsafe fn partial_pop_stack(stack: &mut Vec<Value>) -> Value {
        stack.pop().unwrap_unchecked()
    }

    unsafe fn last_stack(&self) -> &Value {
        self.stack.last().unwrap_unchecked()
    }

    fn new(bytecode: &'a [u8], stdout: W) -> Self {
        let mut reader = BytecodeReader::new(bytecode);
        let version = u32::from_le_bytes(*reader.read::<4>());
        assert_eq!(version, VERSION);

        let len_consts = u32::from_le_bytes(*reader.read::<4>()) as usize;
        reader.bytes = &reader.bytes[reader.head..];
        let consts = std::str::from_utf8(&reader.bytes[..len_consts]).unwrap();
        let instructions = &reader.bytes[len_consts..];

        let stack = vec![];
        let call_stack = vec![];
        let mut variable_stacks: Vec<Vec<Value>> = vec![vec![]];
        variable_stacks[0].extend(Builtin::ALL.map(|b| Value::Callable(Callable::Builtin(b))));

        Self { consts, instructions, head: 0, stack, call_stack, variable_stacks, stdout }
    }

    unsafe fn execute(&mut self) -> io::Result<()> {
        macro_rules! str_literal {
            ($ptr: expr, $len: expr) => {{
                let ptr = $ptr;
                &self.consts[ptr as usize..ptr as usize + $len as usize]
            }};
        }

        while self.head < self.instructions.len() {
            let op = Op::bc_read(&self.instructions[self.head..]);
            self.head += 1 + op.size();
            match op {
                Op::SetStackSize(size) => {
                    let stack = self.variable_stacks.last_mut().unwrap_unchecked();
                    stack.resize_with(size as usize, || Value::Null);
                }
                Op::BuildFstr { num_segments } => {
                    let mut builder = String::new();
                    let remaining = self.pop_stack();
                    for _ in 0..num_segments {
                        let value = self.pop_stack();
                        let Value::String(PettyStr::Literal { ptr, len }) = self.pop_stack() else {
                            panic!()
                        };
                        builder.push_str(str_literal!(ptr, len));
                        let _ = write!(builder, "{}", DisplayValue {
                            value: &value,
                            consts: self.consts
                        });
                    }
                    let Value::String(PettyStr::Literal { ptr, len }) = remaining else { panic!() };
                    builder.push_str(str_literal!(ptr, len));
                    self.stack.push(Value::String(PettyStr::String(Rc::new(builder.into()))));
                }
                Op::CreateMap => self.stack.push(Value::Map(Rc::default())),
                Op::InsertMap => {
                    let value = self.pop_stack();
                    let key = self.pop_stack();
                    let Value::Map(map) = self.stack.last_mut().unwrap() else { panic!() };
                    map.borrow_mut().insert(key, value);
                }
                Op::CreateArray => self.stack.push(Value::Array(Rc::default())),
                Op::ArrayPush => {
                    let value = self.pop_stack();
                    let arr = self.stack.last_mut().unwrap();
                    let Value::Array(arr) = arr else { panic!() };
                    arr.borrow_mut().push(value);
                }
                Op::LoadGlobal(offset) => {
                    self.stack.push(self.variable_stacks[0][offset as usize].clone())
                }
                Op::Load(offset) => {
                    self.stack.push(self.variable_stacks.last().unwrap()[offset as usize].clone())
                }
                Op::Store(offset) => {
                    let offset = offset as usize;
                    let variable_stack = self.variable_stacks.last_mut().unwrap_unchecked();
                    unsafe { assert_unchecked(offset < variable_stack.len()) };
                    variable_stack[offset] = Self::partial_pop_stack(&mut self.stack);
                }
                Op::LoadChar(char) => self.stack.push(Value::Char(char)),
                Op::LoadInt(int) => self.stack.push(Value::Int(int)),
                Op::LoadString { ptr, len } => {
                    self.stack.push(Value::String(PettyStr::Literal { ptr, len }))
                }
                Op::Range => {
                    let end = self.pop_int();
                    let start = self.pop_int();
                    self.stack.push(Value::Range(Rc::new([Cell::new(start), Cell::new(end)])));
                }
                Op::RangeInclusive => {
                    let end = self.pop_int();
                    let start = self.pop_int();
                    self.stack
                        .push(Value::RangeInclusive(Rc::new([Cell::new(start), Cell::new(end)])));
                }
                Op::IterRange => {
                    let Value::Range(range) = self.last_stack() else { unreachable_unchecked() };
                    let [start, end] = &*range.clone();
                    if start.get() < end.get() {
                        self.stack.push(Value::Int(start.get()));
                        self.stack.push(Value::Bool(true));
                        start.set(start.get() + 1);
                    } else {
                        self.stack.push(Value::Bool(false));
                    }
                }
                Op::IterRangeInclusive => {
                    let Value::RangeInclusive(range) = self.last_stack() else {
                        unreachable_unchecked()
                    };
                    let [start, end] = &*range.clone();
                    if start.get() <= end.get() {
                        self.stack.push(Value::Int(start.get()));
                        self.stack.push(Value::Bool(true));
                        start.set(start.get() + 1);
                    } else {
                        self.stack.push(Value::Bool(false));
                    }
                }
                Op::CJump(label) => {
                    if !self.pop_bool() {
                        self.head = label as usize;
                    }
                }
                Op::FnCall { numargs } => 'fn_call: {
                    let Value::Callable(callable) = self.pop_stack() else { panic!() };
                    let value = match callable {
                        Callable::Builtin(builtin) => match builtin {
                            Builtin::Assert => {
                                assert_eq!(numargs, 1);
                                let bool = self.pop_bool();
                                assert!(bool, "RUNTIME ASSERTION FAILED");
                                Value::Bool(bool)
                            }
                            Builtin::Println => {
                                assert_eq!(numargs, 1);
                                let Value::String(str) = self.pop_stack() else { panic!() };
                                self.stdout.write_all(str.as_str(self.consts).as_bytes())?;
                                self.stdout.write_all(b"\n")?;
                                Value::Null
                            }
                            Builtin::ReadFile => {
                                assert_eq!(numargs, 1);
                                let str = self.pop_str();
                                let string =
                                    std::fs::read_to_string(str.as_str(self.consts)).unwrap();
                                Value::String(PettyStr::String(Rc::new(string.into())))
                            }
                            Builtin::Exit => {
                                assert!(numargs <= 1);
                                let int = if numargs == 1 { self.pop_int() as i32 } else { 0 };
                                std::process::exit(int)
                            }
                        },
                        Callable::MethodBuiltin(method) => match method {
                            MethodBuiltin::CharIsAlphabetic(char) => {
                                Value::Bool(char.is_alphabetic())
                            }
                            MethodBuiltin::CharIsDigit(char) => Value::Bool(char.is_ascii_digit()),
                            MethodBuiltin::StrTrim { trimmed } => {
                                Value::String(PettyStr::String(trimmed))
                            }
                            MethodBuiltin::StrIsAlphabetic(str) => Value::Bool(
                                str.as_str(self.consts).chars().all(|c| c.is_ascii_alphabetic()),
                            ),
                            MethodBuiltin::StrIsDigit(str) => Value::Bool(
                                str.as_str(self.consts).chars().all(|c| c.is_ascii_digit()),
                            ),
                            MethodBuiltin::StrStartsWith(str) => {
                                assert_eq!(numargs, 1);
                                let Value::String(arg) = self.pop_stack() else { panic!() };
                                let arg = arg.as_str(self.consts);
                                let str = str.as_str(self.consts);
                                Value::Bool(str.starts_with(arg))
                            }
                            MethodBuiltin::MapGet(map) => {
                                assert_eq!(numargs, 1);
                                let key = self.pop_stack();
                                // TODO: Is this the right output for unknown key?
                                map.borrow().get(&key).cloned().unwrap_or(Value::Null)
                            }
                            MethodBuiltin::MapInsert(map) => {
                                assert_eq!(numargs, 2);
                                let value = self.pop_stack();
                                let key = self.pop_stack();
                                map.borrow_mut().insert(key, value);
                                Value::Null
                            }
                            MethodBuiltin::MapRemove(map) => {
                                assert_eq!(numargs, 1);
                                let key = self.pop_stack();
                                map.borrow_mut().remove(&key);
                                Value::Null
                            }
                            MethodBuiltin::ArrayPush(arr) => {
                                assert_eq!(numargs, 1);
                                let value = self.pop_stack();
                                arr.borrow_mut().push(value);
                                Value::Null
                            }
                            MethodBuiltin::ArrayPop(arr) => {
                                assert_eq!(numargs, 0);
                                // TODO: Is this the right output for an empty array?
                                arr.borrow_mut().pop().unwrap_or(Value::Null)
                            }
                        },
                        Callable::Function { label } => {
                            self.variable_stacks.push(vec![]);
                            let here = self.head;
                            self.call_stack.push(here);
                            self.head = label as usize;
                            break 'fn_call;
                        }
                    };
                    self.stack.push(value);
                }
                Op::Pop => _ = self.pop_stack(),
                Op::Dup => self.stack.push(self.last_stack().clone()),
                Op::Jump(label) => self.head = label as usize,
                Op::Mod => {
                    let rhs = self.pop_int();
                    let lhs = self.pop_int();
                    self.stack.push(Value::Int(lhs % rhs));
                }
                Op::Eq(tag) => {
                    let rhs = self.pop_stack();
                    let lhs = self.pop_stack();
                    macro_rules! glue {
                        ($typ: tt) => {{
                            let Value::$typ(lhs) = lhs else { unreachable_unchecked() };
                            let Value::$typ(rhs) = rhs else { unreachable_unchecked() };
                            self.stack.push(Value::Bool(lhs == rhs));
                        }};
                    }
                    match tag {
                        EqTag::Int => glue!(Int),
                        EqTag::Bool => glue!(Bool),
                        EqTag::Char => glue!(Char),
                        EqTag::Str => {
                            let Value::String(lhs) = lhs else { unreachable_unchecked() };
                            let Value::String(rhs) = rhs else { unreachable_unchecked() };
                            self.stack.push(Value::Bool(
                                lhs.as_str(self.consts) == rhs.as_str(self.consts),
                            ));
                        }
                    }
                }
                Op::Less(tag) => {
                    let rhs = self.pop_stack();
                    let lhs = self.pop_stack();
                    macro_rules! glue {
                        ($typ: tt) => {{
                            let Value::$typ(lhs) = lhs else { unreachable_unchecked() };
                            let Value::$typ(rhs) = rhs else { unreachable_unchecked() };
                            self.stack.push(Value::Bool(lhs < rhs));
                        }};
                    }
                    match tag {
                        EqTag::Int => glue!(Int),
                        EqTag::Bool => glue!(Bool),
                        EqTag::Char => glue!(Char),
                        EqTag::Str => {
                            let Value::String(lhs) = lhs else { unreachable_unchecked() };
                            let Value::String(rhs) = rhs else { unreachable_unchecked() };
                            self.stack.push(Value::Bool(
                                lhs.as_str(self.consts) < rhs.as_str(self.consts),
                            ));
                        }
                    }
                }
                Op::Greater(tag) => {
                    let rhs = self.pop_stack();
                    let lhs = self.pop_stack();
                    macro_rules! glue {
                        ($typ: tt) => {{
                            let Value::$typ(lhs) = lhs else { unreachable_unchecked() };
                            let Value::$typ(rhs) = rhs else { unreachable_unchecked() };
                            self.stack.push(Value::Bool(lhs > rhs));
                        }};
                    }
                    match tag {
                        EqTag::Int => glue!(Int),
                        EqTag::Bool => glue!(Bool),
                        EqTag::Char => glue!(Char),
                        EqTag::Str => {
                            let Value::String(lhs) = lhs else { unreachable_unchecked() };
                            let Value::String(rhs) = rhs else { unreachable_unchecked() };
                            self.stack.push(Value::Bool(
                                lhs.as_str(self.consts) > rhs.as_str(self.consts),
                            ));
                        }
                    }
                }
                Op::Add => {
                    let rhs = self.pop_int();
                    let lhs = self.pop_int();
                    self.stack.push(Value::Int(lhs + rhs));
                }
                Op::AddInt => {
                    let Value::Int(lhs) = self.pop_stack() else { unreachable_unchecked() };
                    let Value::Int(rhs) = self.pop_stack() else { unreachable_unchecked() };
                    self.stack.push(Value::Int(lhs + rhs));
                }
                Op::LoadTrue => self.stack.push(Value::Bool(true)),
                Op::LoadFalse => self.stack.push(Value::Bool(false)),
                Op::CreateFunction => self
                    .stack
                    .push(Value::Callable(Callable::Function { label: self.head as u32 + 5 + 5 })),
                Op::LoadNull => self.stack.push(Value::Null),
                Op::Ret => {
                    self.head = self.call_stack.pop().unwrap();
                    self.variable_stacks.pop().unwrap();
                }
                Op::StoreField(field) => {
                    let value = self.pop_stack();
                    let Value::Struct { fields } = self.stack.last_mut().unwrap() else {
                        unimplemented!("{:?}", self.stack.last().unwrap())
                    };
                    fields.borrow_mut().insert(field, value);
                }
                Op::StoreEnumVariant(variant) => {
                    let Value::Struct { fields } = self.stack.last_mut().unwrap() else {
                        unreachable_unchecked()
                    };
                    fields
                        .borrow_mut()
                        .insert(variant, Value::EnumVariant { name: variant, key: 0 });
                }
                Op::EmptyStruct => self.stack.push(Value::Struct { fields: Rc::default() }),
                Op::LoadField(field) => {
                    let value = match self.pop_stack() {
                        Value::Struct { fields } => match fields.borrow().get(&field) {
                            Some(value) => value.clone(),
                            None => unreachable_unchecked(),
                        },
                        Value::String(str) => load_str_field(self.consts, str, field),
                        Value::Char(char) => load_char_field(self.consts, char, field),
                        Value::Map(map) => load_map_field(self.consts, map, field),
                        Value::Array(arr) => load_array_field(self.consts, arr, field),
                        other => panic!("{other:?}"),
                    };
                    self.stack.push(value);
                }
                Op::Index => {
                    let rhs = self.pop_stack();
                    let lhs = self.pop_stack();
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
                            let Value::Int(rhs) = rhs else { unreachable_unchecked() };
                            arr.borrow()[rhs as usize].clone()
                        }
                        _ => todo!("{lhs:?}"),
                    };
                    self.stack.push(value);
                }
                Op::Not => {
                    let bool = self.pop_bool();
                    self.stack.push(Value::Bool(!bool));
                }
                Op::Neg => {
                    let int = self.pop_int();
                    self.stack.push(Value::Int(-int));
                }
            }
        }
        Ok(())
    }
}

fn load_array_field(consts: &str, arr: Rc<RefCell<Vec<Value>>>, field: StrIdent) -> Value {
    let field = &consts[field.ptr as usize..field.ptr as usize + field.len as usize];
    Value::Callable(Callable::MethodBuiltin(match field {
        "push" => MethodBuiltin::ArrayPush(arr),
        "pop" => MethodBuiltin::ArrayPop(arr),
        _ => panic!("map does not contain field: {}", field),
    }))
}

fn load_map_field(consts: &str, map: Rc<RefCell<PettyMap>>, field: StrIdent) -> Value {
    let field = &consts[field.ptr as usize..field.ptr as usize + field.len as usize];
    Value::Callable(Callable::MethodBuiltin(match field {
        "get" => MethodBuiltin::MapGet(map),
        "insert" => MethodBuiltin::MapInsert(map),
        "remove" => MethodBuiltin::MapRemove(map),
        _ => panic!("map does not contain field: {}", field),
    }))
}

fn load_char_field(consts: &str, char: char, field: StrIdent) -> Value {
    let field = &consts[field.ptr as usize..field.ptr as usize + field.len as usize];
    Value::Callable(Callable::MethodBuiltin(match field {
        "is_digit" => MethodBuiltin::CharIsDigit(char),
        "is_alphabetic" => MethodBuiltin::CharIsAlphabetic(char),
        _ => panic!("char does not contain field: {}", field),
    }))
}

fn load_str_field(consts: &str, string: PettyStr, field: StrIdent) -> Value {
    let field = &consts[field.ptr as usize..field.ptr as usize + field.len as usize];
    let str = string.as_str(consts);
    Value::Callable(Callable::MethodBuiltin(match (field, string.clone()) {
        ("len", _) => return Value::Int(str.len() as i64),
        ("trim", _) => {
            let trimmed = Rc::new(str.trim().into());
            MethodBuiltin::StrTrim { trimmed }
        }
        ("starts_with", str) => MethodBuiltin::StrStartsWith(str),
        ("is_digit", str) => MethodBuiltin::StrIsDigit(str),
        ("is_alphabetic", str) => MethodBuiltin::StrIsAlphabetic(str),
        _ => panic!("str does not contain field: {}", field),
    }))
}

#[derive(Clone, Copy)]
struct DisplayValue<'a, 'b> {
    consts: &'a str,
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
                    debug_map.entry(&DisplayValue { value: key, ..*self }, &DisplayValue {
                        value,
                        ..*self
                    });
                }

                debug_map.finish()
            }
            Value::EnumVariant { name: StrIdent { ptr, len }, .. } => {
                write!(f, "{}", &self.consts[*ptr as usize..*ptr as usize + *len as usize])
            }
            Value::Char(char) => write!(f, "{char}"),
            Value::Struct { fields } => {
                write!(f, "{{")?;
                for (i, (key, value)) in fields.borrow().iter().enumerate() {
                    let key = &self.consts[key.ptr as usize..key.ptr as usize + key.len as usize];
                    let prefix = if i != 0 { "," } else { "" };
                    write!(f, "{prefix} {key}: {}", DisplayValue { value, ..*self })?;
                }
                write!(f, " }}")
            }
            Value::Callable(Callable::Function { label }) => write!(f, "Function at {label}"),
            Value::Callable(Callable::Builtin(function)) => write!(f, "Function: {function:?}"),
            Value::Callable(Callable::MethodBuiltin(method)) => write!(f, "Method: {method:?}"),
            Value::Null => write!(f, "null"),
            Value::Bool(bool) => write!(f, "{bool}"),
            Value::Int(int) => write!(f, "{int}"),
            Value::Range(range) => write!(f, "{}..{}", range[0].get(), range[1].get()),
            Value::RangeInclusive(range) => {
                write!(f, "{}..={}", range[0].get(), range[1].get())
            }
            Value::String(str) => write!(f, "{}", &str.as_str(self.consts)),
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
