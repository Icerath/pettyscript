#![expect(unsafe_op_in_unsafe_fn, reason = "I'm lazy")]

mod value;
mod variable_stack;

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

use value::{Callable, PettyMap, PettyStr, Value};
use variable_stack::VariableStack;

use crate::{
    builtints::{Builtin, MethodBuiltin},
    bytecode::{Instr, StrIdent, VERSION},
};

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

struct VirtualMachine<'src, 'io> {
    consts: &'src str,
    instructions: &'src [u8],
    head: usize,
    stack: Vec<Value<'src>>,
    call_stack: Vec<usize>,
    variable_stacks: VariableStack<'src>,
    stdout: &'io mut dyn Write,
}

macro_rules! impl_pop_helper {
    ($name:ident, $variant:ident, $typ:ty) => {
        unsafe fn $name(&mut self) -> $typ {
            match self.pop_stack() {
                Value::$variant(inner) => inner,
                _ => unreachable_unchecked(),
            }
        }
    };
}

impl<'src, 'io> VirtualMachine<'src, 'io> {
    impl_pop_helper! { pop_int, Int, i64 }

    impl_pop_helper! { pop_bool, Bool, bool }

    impl_pop_helper! { pop_char, Char, char }

    impl_pop_helper! { pop_str, String, PettyStr<'src> }

    impl_pop_helper! { pop_arr, Array, Rc<RefCell<Vec<Value<'src>>>> }

    impl_pop_helper! { pop_map, Map, Rc<RefCell<PettyMap<'src>>> }

    unsafe fn pop_stack(&mut self) -> Value<'src> {
        Self::partial_pop_stack(&mut self.stack)
    }

    unsafe fn partial_pop_stack(stack: &mut Vec<Value<'src>>) -> Value<'src> {
        stack.pop().unwrap_unchecked()
    }

    unsafe fn last_stack(&self) -> &Value<'src> {
        self.stack.last().unwrap_unchecked()
    }

    unsafe fn last_stack_mut(&mut self) -> &mut Value<'src> {
        self.stack.last_mut().unwrap_unchecked()
    }

    fn new(bytecode: &'src [u8], stdout: &'io mut dyn Write) -> Self {
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

        let mut variable_stacks = VariableStack::default();
        let global_scope = Builtin::ALL
            .map(|b| Value::Callable(Callable::Builtin(b)))
            .into_iter()
            .chain((0..global_stack_size - Builtin::ALL.len()).map(|_| Value::Bool(false)));
        variable_stacks.extend_new(global_scope);
        Self { consts, instructions, head: 0, stack, call_stack, variable_stacks, stdout }
    }

    #[expect(clippy::too_many_lines)]
    unsafe fn execute(&mut self) -> io::Result<()> {
        while self.head < self.instructions.len() {
            let op = Instr::bc_read_unchecked(&self.instructions[self.head..]);
            self.head += 1 + op.size();
            match op {
                Instr::EnumTag => {
                    let Value::EnumVariant { tag } = self.pop_stack() else {
                        unreachable_unchecked()
                    };
                    self.stack.push(Value::Int(tag as i64));
                }
                Instr::Abort => panic!("ABORTING"),
                Instr::BuildFstr { num_segments } => {
                    let mut builder = String::new();
                    for value in self.stack.drain(self.stack.len() - num_segments as usize..) {
                        let _ = write!(builder, "{}", DisplayValue { value: &value });
                    }
                    self.stack.push(Value::String(PettyStr::String(Rc::new(builder.into()))));
                }
                Instr::CreateMap { num_keys } => {
                    // TODO: Restrict key types and use hashmap.
                    #[expect(clippy::mutable_key_type)]
                    let mut map = BTreeMap::new();
                    for _ in 0..num_keys {
                        let value = self.pop_stack();
                        let key = self.pop_stack();
                        map.insert(key, value);
                    }
                    self.stack.push(Value::Map(Rc::new(RefCell::new(map))));
                }
                Instr::CreateArray { size } => {
                    let arr = self.stack.drain((self.stack.len() - size as usize)..).collect();
                    self.stack.push(Value::Array(Rc::new(RefCell::new(arr))));
                }
                Instr::ArrayConcatStack => {
                    let arr = self.pop_arr();
                    self.stack.extend_from_slice(&arr.borrow());
                }
                Instr::LoadGlobal(offset) => {
                    let stack = self.variable_stacks.first();
                    unsafe { assert_unchecked((offset as usize) < stack.len()) };
                    self.stack.push(stack[offset as usize].clone());
                }
                Instr::Load(offset) => {
                    let stack = self.variable_stacks.last();
                    unsafe { assert_unchecked((offset as usize) < stack.len()) };
                    self.stack.push(stack[offset as usize].clone());
                }
                Instr::Store(offset) => {
                    let offset = offset as usize;
                    let variable_stack = self.variable_stacks.last();
                    unsafe { assert_unchecked(offset < variable_stack.len()) };
                    variable_stack[offset] = Self::partial_pop_stack(&mut self.stack);
                }
                Instr::LoadChar(char) => self.stack.push(Value::Char(char)),
                Instr::LoadIntSmall(int) => self.stack.push(Value::Int(int as i64)),
                Instr::LoadInt(int) => self.stack.push(Value::Int(int)),
                Instr::LoadString(StrIdent { ptr, len }) => {
                    self.stack.push(Value::String(PettyStr::Literal(
                        &self.consts[ptr as usize..ptr as usize + len as usize],
                    )));
                }
                Instr::Range => {
                    let end = self.pop_int();
                    let start = self.pop_int();
                    self.stack.push(Value::Range([start, end]));
                }
                Instr::RangeInclusive => {
                    let end = self.pop_int();
                    let start = self.pop_int();
                    self.stack.push(Value::Range([start, end + 1]));
                }
                Instr::IterRange => {
                    let Value::Range([start, end]) = self.last_stack_mut() else {
                        unreachable_unchecked()
                    };
                    if start < end {
                        *start += 1;
                        let start = *start - 1;
                        self.stack.push(Value::Int(start));
                        self.stack.push(Value::Bool(true));
                    } else {
                        self.stack.push(Value::Bool(false));
                    }
                }
                Instr::CJump(label) => {
                    if !self.pop_bool() {
                        self.head = label as usize;
                    }
                }
                Instr::FnCall => 'fn_call: {
                    let Value::Callable(callable) = self.pop_stack() else {
                        unreachable_unchecked()
                    };
                    let value = match callable {
                        Callable::Builtin(builtin) => match builtin {
                            Builtin::ParseInt => {
                                let str = self.pop_str();
                                Value::Int(str.parse::<i64>().unwrap())
                            }
                            Builtin::Assert => {
                                let bool = self.pop_bool();
                                assert!(bool, "RUNTIME ASSERTION FAILED");
                                Value::Bool(bool)
                            }
                            Builtin::Println => {
                                let str = self.pop_str();
                                self.stdout.write_all(str.as_bytes())?;
                                self.stdout.write_all(b"\n")?;
                                break 'fn_call;
                            }
                            Builtin::ReadFile => {
                                let str = self.pop_str();
                                let string = std::fs::read_to_string(str.as_str()).unwrap();
                                Value::String(PettyStr::String(Rc::new(string.into())))
                            }
                            Builtin::Exit => {
                                let int = self.pop_int() as i32;
                                std::process::exit(int)
                            }
                        },
                        Callable::Function { label, stack_size } => {
                            self.variable_stacks
                                .extend_new((0..stack_size).map(|_| Value::Bool(false)));
                            let here = self.head;
                            self.call_stack.push(here);
                            self.head = label as usize;
                            break 'fn_call;
                        }
                    };
                    self.stack.push(value);
                }
                Instr::Pop => _ = self.pop_stack(),
                Instr::Dup => self.stack.push(self.last_stack().clone()),
                Instr::Jump(label) => self.head = label as usize,
                Instr::Mod => {
                    let rhs = self.pop_int();
                    let lhs = self.pop_int();
                    self.stack.push(Value::Int(lhs % rhs));
                }
                Instr::Greater => {
                    let is_greater = self.cmp() == Ordering::Greater;
                    self.stack.push(Value::Bool(is_greater));
                }
                Instr::Less => {
                    let is_greater = self.cmp() == Ordering::Less;
                    self.stack.push(Value::Bool(is_greater));
                }
                Instr::Eq => {
                    let is_greater = self.cmp() == Ordering::Equal;
                    self.stack.push(Value::Bool(is_greater));
                }
                Instr::AddInt => {
                    let rhs = self.pop_int();
                    let lhs = self.pop_int();
                    self.stack.push(Value::Int(lhs + rhs));
                }
                Instr::SubInt => {
                    let rhs = self.pop_int();
                    let lhs = self.pop_int();
                    self.stack.push(Value::Int(lhs - rhs));
                }
                Instr::MulInt => {
                    let rhs = self.pop_int();
                    let lhs = self.pop_int();
                    self.stack.push(Value::Int(lhs * rhs));
                }
                Instr::DivInt => {
                    let rhs = self.pop_int();
                    let lhs = self.pop_int();
                    self.stack.push(Value::Int(lhs / rhs));
                }
                Instr::LoadBool(bool) => self.stack.push(Value::Bool(bool)),
                Instr::CreateFunction { stack_size } => {
                    self.stack.push(Value::Callable(Callable::Function {
                        label: self.head as u32 + 5 + 5,
                        stack_size,
                    }));
                }
                Instr::Ret => {
                    self.head = self.call_stack.pop().unwrap();
                    self.variable_stacks.pop();
                }
                Instr::StoreField(field) => {
                    let value = self.pop_stack();
                    let Value::Struct { fields } = self.stack.last_mut().unwrap() else {
                        unreachable_unchecked()
                    };
                    fields.borrow_mut()[field as usize] = value;
                }
                Instr::LoadVariant { tag } => self.stack.push(Value::EnumVariant { tag }),
                Instr::CreateStruct { size } => {
                    let fields: Box<[Value]> =
                        std::iter::repeat_with(|| Value::Bool(false)).take(size as usize).collect();
                    let fields = Rc::new(RefCell::new(fields));
                    self.stack.push(Value::Struct { fields });
                }
                Instr::CallBuiltinMethod(method) => self.call_builtin_method(method),
                Instr::LoadField(field) => {
                    let Value::Struct { fields } = self.pop_stack() else {
                        unreachable_unchecked()
                    };
                    let value = match fields.borrow().get(field as usize) {
                        Some(value) => value.clone(),
                        None => unreachable_unchecked(),
                    };
                    self.stack.push(value);
                }
                Instr::ArrayIndex => {
                    let rhs = self.pop_int();
                    let lhs = self.pop_arr();
                    self.stack.push(lhs.borrow()[rhs as usize].clone());
                }
                Instr::StringIndex => {
                    let rhs = self.pop_int();
                    let lhs = self.pop_str();
                    // TODO: Better string api.
                    self.stack.push(Value::Char(lhs.chars().nth(rhs as usize).unwrap()));
                }
                Instr::StringSliceRange => {
                    let Value::Range([start, end]) = self.pop_stack() else {
                        unreachable_unchecked()
                    };
                    let range = start as usize..end as usize;
                    let str = match self.pop_str() {
                        PettyStr::Literal(str) => PettyStr::Literal(&str[range]),
                        PettyStr::String(str) => PettyStr::String(Rc::new(str[range].into())),
                    };
                    self.stack.push(Value::String(str));
                }
                Instr::Not => {
                    let bool = self.pop_bool();
                    self.stack.push(Value::Bool(!bool));
                }
                Instr::Neg => {
                    let int = self.pop_int();
                    self.stack.push(Value::Int(-int));
                }
            }
        }
        debug_assert!(
            self.stack.is_empty(),
            "len: {}\n{:?}",
            self.stack.len(),
            self.stack.last().unwrap()
        );
        Ok(())
    }

    unsafe fn cmp(&mut self) -> Ordering {
        let rhs = self.pop_stack();
        let lhs = self.pop_stack();
        macro_rules! glue {
            ($typ:tt, $lhs:ident) => {{
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
                lhs.as_str().cmp(rhs.as_str())
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

            M::StrLen => Value::Int(self.pop_str().len() as i64),
            M::StrIsAlphabetic => {
                let str = self.pop_str();
                Value::Bool(str.chars().all(|c| c.is_ascii_alphabetic()))
            }
            M::StrIsDigit => Value::Bool(self.pop_str().chars().all(|c| c.is_ascii_digit())),
            M::StrTrim => Value::String(PettyStr::String(Rc::new(self.pop_str().trim().into()))),
            M::StrStartsWith => {
                let pat = self.pop_str();
                let str = self.pop_str();
                Value::Bool(str.starts_with(pat.as_str()))
            }
            M::StrLines => Value::Array(Rc::new(
                self.pop_str()
                    .lines()
                    .map(|s| Value::String(PettyStr::String(Rc::new(s.into()))))
                    .collect::<Vec<_>>()
                    .into(),
            )),

            M::ArrayLen => Value::Int(self.pop_arr().borrow().len() as i64),
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
            M::MapContains => {
                let key = self.pop_stack();
                let map = self.pop_map();
                Value::Bool(map.borrow_mut().contains_key(&key))
            }
        };
        self.stack.push(value);
    }
}

#[derive(Clone, Copy)]
struct DisplayValue<'src, 'b> {
    value: &'b Value<'src>,
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
                    debug_map.entry(&DisplayValue { value: key }, &DisplayValue { value });
                }

                debug_map.finish()
            }
            Value::EnumVariant { tag } => unreachable!("{tag}"),
            Value::Char(char) => write!(f, "{char}"),
            Value::Struct { fields } => {
                write!(f, "{{")?;
                for (i, value) in fields.borrow().iter().enumerate() {
                    let prefix = if i != 0 { "," } else { "" };
                    write!(f, "{prefix} {}", DisplayValue { value })?;
                }
                write!(f, " }}")
            }
            Value::Callable(Callable::Function { label, stack_size: _ }) => {
                write!(f, "Function at {label}")
            }
            Value::Callable(Callable::Builtin(function)) => write!(f, "Function: {function:?}"),
            Value::Bool(bool) => write!(f, "{bool}"),
            Value::Int(int) => write!(f, "{int}"),
            Value::Range([start, end]) => write!(f, "{start}..{end}"),
            Value::String(str) => write!(f, "{}", &str.as_str()),
            Value::Array(values) => {
                let mut debug_list = f.debug_list();
                for value in &*values.borrow() {
                    debug_list.entry(&format_args!("{}", DisplayValue { value }));
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
