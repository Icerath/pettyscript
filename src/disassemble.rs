use crate::{
    bytecode::{Op, VERSION},
    vm::BytecodeReader,
};

pub fn disassemble(bytecode: &[u8]) {
    let mut reader = BytecodeReader::new(bytecode);
    let version = u32::from_le_bytes(*reader.read::<4>());
    let _global_stack_size = u32::from_le_bytes(*reader.read::<4>());
    assert_eq!(version, VERSION);
    let len_consts = u32::from_le_bytes(*reader.read::<4>()) as usize;
    reader.bytes = &reader.bytes[reader.head..];
    reader.head = 0;
    let consts = std::str::from_utf8(&reader.bytes[..len_consts]).unwrap();
    reader.bytes = &reader.bytes[len_consts..];

    macro_rules! load_ident {
        ($ident: ident) => {
            &consts[$ident.ptr as usize..$ident.ptr as usize + $ident.len as usize]
        };
    }

    while reader.head < reader.bytes.len() {
        let offset = reader.head;
        let op = Op::bc_read(&reader.bytes[reader.head..]);
        reader.head += 1 + op.size();
        print!("{offset}: ");
        match op {
            Op::Abort => println!("ABORT"),
            Op::BuildFstr { num_segments } => println!("BUILD_FSTR {num_segments:?}"),
            Op::AddInt => println!("ADD_INT"),
            Op::Neg => println!("NEG"),
            Op::CreateMap => println!("CREATE_MAP"),
            Op::InsertMap => println!("INSERT_MAP"),
            Op::CreateArray => println!("CREATE_ARRAY"),
            Op::ArrayPush => println!("ARRAY_PUSH"),
            Op::Dup => println!("DUP"),
            Op::Eq(tag) => println!("EQ {}", tag as u8),
            Op::Less(tag) => println!("LESS {}", tag as u8),
            Op::Greater(tag) => println!("GREATER {}", tag as u8),
            Op::Index => println!("INDEX"),
            Op::Jump(label) => println!("JUMP {label}"),
            Op::CJump(label) => println!("CJUMP {label}"),
            Op::CreateFunction { stack_size } => println!("CREATE_FUNCTION {stack_size}"),
            Op::EmptyStruct => println!("EMPTY_STRUCT"),
            Op::FnCall => println!("FN_CALL"),
            Op::IterRange => println!("ITER_RANGE"),
            Op::IterRangeInclusive => println!("ITER_RANGE_INCLUSIVE"),
            Op::Load(ident) => println!("LOAD {ident}"),
            Op::Store(ident) => println!("STORE {ident}"),
            Op::LoadChar(char) => println!("LOAD_CHAR '{char}'"),
            Op::LoadFalse => println!("LOAD_FALSE"),
            Op::LoadTrue => println!("LOAD_TRUE"),
            Op::Pop => println!("POP"),
            Op::LoadField(field) => println!("LOAD_FIELD {}", load_ident!(field)),
            Op::LoadBuiltinField(field) => println!("LOAD_FIELD {}", field as u8),
            Op::StoreField(field) => println!("STORE_FIELD {}", load_ident!(field)),
            Op::LoadGlobal(global) => println!("LOAD_GLOBAL {global}"),
            Op::LoadIntSmall(int) => println!("LOAD_INT_SMALL {int}"),
            Op::LoadInt(int) => println!("LOAD_INT {int}"),
            Op::LoadNull => println!("LOAD_NULL"),
            Op::LoadString { ptr, len } => println!("LOAD_STR {ptr} {len}"),
            Op::Mod => println!("MODULO"),
            Op::Not => println!("NOT"),
            Op::Range => println!("RANGE"),
            Op::RangeInclusive => println!("RANGE_INCLUSIVE"),
            Op::Ret => println!("RET"),
            Op::StoreEnumVariant(ident) => println!("SET_VARIANT {}", load_ident!(ident)),
        };
    }
}
