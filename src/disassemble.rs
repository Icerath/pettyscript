use crate::{
    bytecode::{Op, VERSION},
    vm::BytecodeReader,
};
use bstr::ByteSlice;

pub fn disassemble(bytecode: &[u8]) {
    let mut reader = BytecodeReader::new(bytecode);
    let version = u32::from_le_bytes(*reader.read::<4>());
    assert_eq!(version, VERSION);
    let len_consts = u32::from_le_bytes(*reader.read::<4>()) as usize;
    reader.bytes = &reader.bytes[reader.head..];
    reader.head = 0;
    let consts = &reader.bytes[..len_consts];
    reader.bytes = &reader.bytes[len_consts..];

    macro_rules! load_ident {
        ($ident: ident) => {
            consts[$ident.ptr as usize..$ident.ptr as usize + $ident.len as usize].as_bstr()
        };
    }

    while reader.head < reader.bytes.len() {
        let offset = reader.head;
        let op = Op::bc_read(&reader.bytes[reader.head..]);
        reader.head += 1 + op.size();
        print!("x{offset:x}: ");
        match op {
            Op::Add => println!("ADD"),
            Op::Dup => println!("DUP"),
            Op::Eq => println!("EQ"),
            Op::Index => println!("INDEX"),
            Op::Less => println!("LESS"),
            Op::Jump(label) => println!("JUMP x{label:x}"),
            Op::CJump(label) => println!("CJUMP x{label:x}"),
            Op::CreateFunction => println!("CREATE_FUNCTION"),
            Op::EmptyStruct => println!("EMPTY_STRUCT"),
            Op::FnCall { numargs } => println!("FN_CALL {numargs}"),
            Op::Greater => println!("GREATER"),
            Op::IterNext => println!("ITER_NEXT"),
            Op::Load(ident) => println!("LOAD {ident}"),
            Op::Store(ident) => println!("STORE {ident}"),
            Op::LoadChar(char) => println!("LOAD_CHAR '{char}'"),
            Op::LoadFalse => println!("LOAD_FALSE"),
            Op::LoadTrue => println!("LOAD_TRUE"),
            Op::Pop => println!("POP"),
            Op::LoadField(field) => println!("LOAD_FIELD {}", load_ident!(field)),
            Op::StoreField(field) => println!("STORE_FIELD {}", load_ident!(field)),
            Op::LoadGlobal(global) => println!("LOAD_GLOBAL {global}"),
            Op::LoadInt(int) => println!("LOAD_INT {int}"),
            Op::LoadNull => println!("LOAD_NULL"),
            Op::LoadString { ptr, len } => println!("LOAD_STR x{ptr:x} {len}"),
            Op::Mod => println!("MODULO"),
            Op::Not => println!("NOT"),
            Op::Range => println!("RANGE"),
            Op::RangeInclusive => println!("RANGE_INCLUSIVE"),
            Op::Ret => println!("RET"),
            Op::StoreEnumVariant(ident) => println!("SET_VARIANT {}", load_ident!(ident)),
        };
    }
}
