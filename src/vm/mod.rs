#![expect(unsafe_op_in_unsafe_fn, reason = "I'm lazy")]

use core::fmt;
use std::{
    cell::RefCell,
    cmp::Ordering,
    collections::BTreeMap,
    fmt::Write as _,
    hint::{assert_unchecked, unreachable_unchecked},
    io::{self, Write},
    rc::Rc,
};

use crate::{
    builtints::{Builtin, BuiltinField, MethodBuiltin},
    bytecode::{Op, StrIdent, VERSION},
};

pub type PettyMap = BTreeMap<Value, Value>;

// TODO: Remove Rc<Refcell> with indexes
// TODO: Replace BTreeMap with HashMap
// TODO: Avoid extra indirection/allocation for Struct.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Value {
    Bool(bool),
    EnumVariant { name: StrIdent },
    Char(char),
    Int(i64),
    Callable(Callable),
    String(PettyStr),
    Array(Rc<RefCell<Vec<Value>>>),
    Map(Rc<RefCell<PettyMap>>),
    Range([i64; 2]),
    RangeInclusive([i64; 2]),
    Struct { fields: Rc<RefCell<Box<[Value]>>> },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Callable {
    Builtin(Builtin),
    Function { label: u32, stack_size: u16 },
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
    let mut stdout = std::io::stdout().lock();
    unsafe { execute_bytecode_with(bytecode, &mut stdout).unwrap() }
}

/// # Safety
/// bytecode must have been generated using codegen
pub unsafe fn execute_bytecode_with(bytecode: &[u8], stdout: &mut dyn Write) -> io::Result<()> {
    unsafe { VirtualMachine::new(bytecode, stdout).execute() }
}

struct VirtualMachine<'a, 'io> {
    consts: &'a str,
    instructions: &'a [u8],
    head: usize,
    stack: Vec<Value>,
    call_stack: Vec<usize>,
    variable_stacks: Vec<Box<[Value]>>,
    stdout: &'io mut dyn Write,
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

impl<'a, 'io> VirtualMachine<'a, 'io> {
    impl_pop_helper! { pop_int, Int, i64 }

    impl_pop_helper! { pop_bool, Bool, bool }

    impl_pop_helper! { pop_char, Char, char }

    impl_pop_helper! { pop_str, String, PettyStr }

    impl_pop_helper! { pop_arr, Array, Rc<RefCell<Vec<Value>>> }

    impl_pop_helper! { pop_map, Map, Rc<RefCell<PettyMap>> }

    unsafe fn pop_stack(&mut self) -> Value {
        Self::partial_pop_stack(&mut self.stack)
    }

    unsafe fn partial_pop_stack(stack: &mut Vec<Value>) -> Value {
        stack.pop().unwrap_unchecked()
    }

    unsafe fn last_stack(&self) -> &Value {
        self.stack.last().unwrap_unchecked()
    }

    fn new(bytecode: &'a [u8], stdout: &'io mut dyn Write) -> Self {
        let mut reader = BytecodeReader::new(bytecode);
        let version = u32::from_le_bytes(*reader.read::<4>());
        assert_eq!(version, VERSION);
        let global_stack_size = u32::from_le_bytes(*reader.read::<4>()) as usize;

        let len_consts = u32::from_le_bytes(*reader.read::<4>()) as usize;
        reader.bytes = &reader.bytes[reader.head..];
        let consts = std::str::from_utf8(&reader.bytes[..len_consts]).unwrap();
        let instructions = &reader.bytes[len_consts..];

        let stack = vec![];
        let call_stack = vec![];

        let global_scope = Builtin::ALL
            .map(|b| Value::Callable(Callable::Builtin(b)))
            .into_iter()
            .chain((0..global_stack_size - Builtin::ALL.len()).map(|_| Value::Bool(false)))
            .collect();
        let variable_stacks: Vec<Box<[Value]>> = vec![global_scope];
        Self { consts, instructions, head: 0, stack, call_stack, variable_stacks, stdout }
    }

    unsafe fn execute(&mut self) -> io::Result<()> {
        while self.head < self.instructions.len() {
            let op = Op::bc_read_unchecked(&self.instructions[self.head..]);
            self.head += 1 + op.size();
            match op {
                Op::Abort => panic!("ABORTING"),
                Op::BuildFstr { num_segments } => {
                    let mut builder = String::new();
                    for _ in 0..num_segments {
                        let value = self.pop_stack();
                        let _ = write!(builder, "{}", DisplayValue {
                            value: &value,
                            consts: self.consts
                        });
                    }
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
                Op::ArrayConcatStack => {
                    let arr = self.pop_arr();
                    self.stack.extend_from_slice(&arr.borrow());
                }
                Op::LoadGlobal(offset) => {
                    unsafe { assert_unchecked(!self.variable_stacks.is_empty()) };
                    let stack = &self.variable_stacks[0];
                    unsafe { assert_unchecked((offset as usize) < stack.len()) };
                    self.stack.push(stack[offset as usize].clone());
                }
                Op::Load(offset) => {
                    let stack = self.variable_stacks.last().unwrap_unchecked();
                    unsafe { assert_unchecked((offset as usize) < stack.len()) };
                    self.stack.push(stack[offset as usize].clone())
                }
                Op::Store(offset) => {
                    let offset = offset as usize;
                    let variable_stack = self.variable_stacks.last_mut().unwrap_unchecked();
                    unsafe { assert_unchecked(offset < variable_stack.len()) };
                    variable_stack[offset] = Self::partial_pop_stack(&mut self.stack);
                }
                Op::LoadChar(char) => self.stack.push(Value::Char(char)),
                Op::LoadIntSmall(int) => self.stack.push(Value::Int(int as i64)),
                Op::LoadInt(int) => self.stack.push(Value::Int(int)),
                Op::LoadString { ptr, len } => {
                    self.stack.push(Value::String(PettyStr::Literal { ptr, len }))
                }
                Op::Range => {
                    let end = self.pop_int();
                    let start = self.pop_int();
                    self.stack.push(Value::Range([start, end]));
                }
                Op::RangeInclusive => {
                    let end = self.pop_int();
                    let start = self.pop_int();
                    self.stack.push(Value::RangeInclusive([start, end]));
                }
                Op::IterRange => {
                    let Value::Range([start, end]) = self.pop_stack() else {
                        unreachable_unchecked()
                    };
                    if start < end {
                        self.stack.push(Value::Range([start + 1, end]));
                        self.stack.push(Value::Int(start));
                        self.stack.push(Value::Bool(true));
                    } else {
                        self.stack.push(Value::Bool(false));
                    }
                }
                Op::IterRangeInclusive => {
                    let Value::RangeInclusive([start, end]) = self.pop_stack() else {
                        unreachable_unchecked()
                    };
                    if start <= end {
                        self.stack.push(Value::RangeInclusive([start + 1, end]));
                        self.stack.push(Value::Int(start));
                        self.stack.push(Value::Bool(true));
                    } else {
                        self.stack.push(Value::Bool(false));
                    }
                }
                Op::CJump(label) => {
                    if !self.pop_bool() {
                        self.head = label as usize;
                    }
                }
                Op::FnCall => 'fn_call: {
                    let Value::Callable(callable) = self.pop_stack() else { panic!() };
                    let value = match callable {
                        Callable::Builtin(builtin) => match builtin {
                            Builtin::ParseInt => {
                                let str = self.pop_str();
                                Value::Int(str.as_str(self.consts).parse::<i64>().unwrap())
                            }
                            Builtin::Assert => {
                                let bool = self.pop_bool();
                                assert!(bool, "RUNTIME ASSERTION FAILED");
                                Value::Bool(bool)
                            }
                            Builtin::Println => {
                                let str = self.pop_str();
                                self.stdout.write_all(str.as_str(self.consts).as_bytes())?;
                                self.stdout.write_all(b"\n")?;
                                break 'fn_call;
                            }
                            Builtin::ReadFile => {
                                let str = self.pop_str();
                                let string =
                                    std::fs::read_to_string(str.as_str(self.consts)).unwrap();
                                Value::String(PettyStr::String(Rc::new(string.into())))
                            }
                            Builtin::Exit => {
                                let int = self.pop_int() as i32;
                                std::process::exit(int)
                            }
                        },
                        Callable::Function { label, stack_size } => {
                            self.variable_stacks
                                .push((0..stack_size).map(|_| Value::Bool(false)).collect());
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
                Op::Greater => {
                    let is_greater = self.cmp() == Ordering::Greater;
                    self.stack.push(Value::Bool(is_greater))
                }
                Op::Less => {
                    let is_greater = self.cmp() == Ordering::Less;
                    self.stack.push(Value::Bool(is_greater))
                }
                Op::Eq => {
                    let is_greater = self.cmp() == Ordering::Equal;
                    self.stack.push(Value::Bool(is_greater))
                }
                Op::AddInt => {
                    let Value::Int(lhs) = self.pop_stack() else { unreachable_unchecked() };
                    let Value::Int(rhs) = self.pop_stack() else { unreachable_unchecked() };
                    self.stack.push(Value::Int(lhs + rhs));
                }
                Op::LoadBool(bool) => self.stack.push(Value::Bool(bool)),
                Op::CreateFunction { stack_size } => {
                    self.stack.push(Value::Callable(Callable::Function {
                        label: self.head as u32 + 5 + 5,
                        stack_size,
                    }))
                }
                Op::Ret => {
                    self.head = self.call_stack.pop().unwrap();
                    self.variable_stacks.pop().unwrap();
                }
                Op::StoreField(field) => {
                    let value = self.pop_stack();
                    let Value::Struct { fields } = self.stack.last_mut().unwrap() else {
                        unreachable_unchecked()
                    };
                    fields.borrow_mut()[field as usize] = value;
                }
                Op::LoadVariant(name) => self.stack.push(Value::EnumVariant { name }),
                Op::CreateStruct { size } => {
                    let fields: Box<[Value]> =
                        std::iter::repeat_with(|| Value::Bool(false)).take(size as usize).collect();
                    let fields = Rc::new(RefCell::new(fields));
                    self.stack.push(Value::Struct { fields })
                }
                Op::CallBuiltinMethod(method) => self.call_builtin_method(method),
                Op::LoadBuiltinField(field) => self.load_builtin_field(field),
                Op::LoadField(field) => {
                    let Value::Struct { fields } = self.pop_stack() else {
                        unreachable_unchecked()
                    };
                    let value = match fields.borrow().get(field as usize) {
                        Some(value) => value.clone(),
                        None => unreachable_unchecked(),
                    };
                    self.stack.push(value);
                }
                Op::Index => {
                    let rhs = self.pop_stack();
                    let lhs = self.pop_stack();
                    let value = match lhs {
                        Value::String(str) => {
                            let str = str.as_str(self.consts);
                            match rhs {
                                Value::Int(x) => Value::Char(str.chars().nth(x as usize).unwrap()),
                                Value::RangeInclusive(_) => todo!(),
                                Value::Range([start, end]) => Value::String(PettyStr::String(
                                    Rc::new(str[start as usize..end as usize].into()),
                                )),
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

    unsafe fn cmp(&mut self) -> Ordering {
        let rhs = self.pop_stack();
        let lhs = self.pop_stack();
        macro_rules! glue {
            ($typ: tt, $lhs: ident) => {{
                let Value::$typ(rhs) = rhs else { unreachable_unchecked() };
                $lhs.cmp(&rhs)
            }};
        }
        match lhs {
            Value::Int(lhs) => glue!(Int, lhs),
            Value::Bool(lhs) => glue!(Bool, lhs),
            Value::Char(lhs) => glue!(Char, lhs),
            Value::String(lhs) => {
                let Value::String(rhs) = rhs else { unreachable_unchecked() };
                lhs.as_str(self.consts).cmp(rhs.as_str(self.consts))
            }
            Value::Array(lhs) => {
                let Value::Array(rhs) = rhs else { unreachable_unchecked() };
                lhs.borrow().cmp(&*rhs.borrow())
            }
            _ => unreachable_unchecked(),
        }
    }

    unsafe fn call_builtin_method(&mut self, method: MethodBuiltin) {
        use MethodBuiltin as M;

        let value = match method {
            M::IntAbs => Value::Int(self.pop_int().abs()),

            M::CharIsDigit => Value::Bool(self.pop_char().is_ascii_digit()),
            M::CharIsAlphabetic => Value::Bool(self.pop_char().is_alphabetic()),

            M::StrIsAlphabetic => {
                let str = self.pop_str();
                Value::Bool(str.as_str(self.consts).chars().all(|c| c.is_ascii_alphabetic()))
            }
            M::StrIsDigit => {
                let str = self.pop_str();
                Value::Bool(str.as_str(self.consts).chars().all(|c| c.is_ascii_digit()))
            }
            M::StrTrim => {
                let str = self.pop_str();
                Value::String(PettyStr::String(Rc::new(str.as_str(self.consts).trim().into())))
            }
            M::StrStartsWith => {
                let pat = self.pop_str();
                let str = self.pop_str();

                let pat = pat.as_str(self.consts);
                let str = str.as_str(self.consts);

                Value::Bool(str.starts_with(pat))
            }

            M::ArrayPop => self.pop_arr().borrow_mut().pop().unwrap(),
            M::ArrayPush => {
                let value = self.pop_stack();
                self.pop_arr().borrow_mut().push(value);
                return;
            }
            M::ArraySortInt => {
                let arr = self.pop_arr();
                arr.borrow_mut().sort();
                Value::Array(arr)
            }
            M::MapInsert => {
                let value = self.pop_stack();
                let key = self.pop_stack();
                let map = self.pop_map();
                map.borrow_mut().insert(key, value);
                return;
            }
            M::MapGet => {
                let key = self.pop_stack();
                let map = self.pop_map();
                map.borrow().get(&key).unwrap().clone()
            }
            M::MapRemove => {
                let key = self.pop_stack();
                let map = self.pop_map();
                map.borrow_mut().remove(&key);
                return;
            }
        };
        self.stack.push(value);
    }

    unsafe fn load_builtin_field(&mut self, field: BuiltinField) {
        use BuiltinField as B;
        let val = match field {
            B::StrLen => Value::Int(self.pop_str().as_str(self.consts).len() as i64),
            B::ArrayLen => Value::Int(self.pop_arr().borrow().len() as i64),
        };
        self.stack.push(val);
    }
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
            Value::EnumVariant { name: StrIdent { ptr, len } } => {
                write!(f, "{}", &self.consts[*ptr as usize..*ptr as usize + *len as usize])
            }
            Value::Char(char) => write!(f, "{char}"),
            Value::Struct { fields } => {
                write!(f, "{{")?;
                for (i, value) in fields.borrow().iter().enumerate() {
                    let prefix = if i != 0 { "," } else { "" };
                    write!(f, "{prefix} {}", DisplayValue { value, ..*self })?;
                }
                write!(f, " }}")
            }
            Value::Callable(Callable::Function { label, stack_size: _ }) => {
                write!(f, "Function at {label}")
            }
            Value::Callable(Callable::Builtin(function)) => write!(f, "Function: {function:?}"),
            Value::Bool(bool) => write!(f, "{bool}"),
            Value::Int(int) => write!(f, "{int}"),
            Value::Range([start, end]) => write!(f, "{}..{}", start, end),
            Value::RangeInclusive([start, end]) => {
                write!(f, "{}..={}", start, end)
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
