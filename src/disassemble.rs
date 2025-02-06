use crate::{
    bytecode::{Instr, VERSION},
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

    macro_rules! load_str {
        ($ptr: expr, $len: expr) => {{
            let ptr = $ptr;
            &consts[ptr as usize..ptr as usize + $len as usize]
        }};
    }

    while reader.head < reader.bytes.len() {
        let offset = reader.head;
        let op = Instr::bc_read(&reader.bytes[reader.head..]);
        reader.head += 1 + op.size();
        print!("{offset}: ");
        match op {
            Instr::Abort => println!("ABORT"),
            Instr::BuildFstr { num_segments } => println!("BUILD_FSTR {num_segments:?}"),
            Instr::AddInt => println!("ADD_INT"),
            Instr::Neg => println!("NEG"),
            Instr::CreateMap => println!("CREATE_MAP"),
            Instr::InsertMap => println!("INSERT_MAP"),
            Instr::CreateArray => println!("CREATE_ARRAY"),
            Instr::ArrayPush => println!("ARRAY_PUSH"),
            Instr::ArrayConcatStack => println!("ARRAY_CONCAT_STACK"),
            Instr::Dup => println!("DUP"),
            Instr::Eq => println!("EQ"),
            Instr::Less => println!("LESS"),
            Instr::Greater => println!("GREATER"),
            Instr::Index => println!("INDEX"),
            Instr::Jump(label) => println!("JUMP {label}"),
            Instr::CJump(label) => println!("CJUMP {label}"),
            Instr::CreateFunction { stack_size } => println!("CREATE_FUNCTION {stack_size}"),
            Instr::CreateStruct { size } => println!("EMPTY_STRUCT {size}"),
            Instr::FnCall => println!("FN_CALL"),
            Instr::IterRange => println!("ITER_RANGE"),
            Instr::IterRangeInclusive => println!("ITER_RANGE_INCLUSIVE"),
            Instr::Load(ident) => println!("LOAD {ident}"),
            Instr::Store(ident) => println!("STORE {ident}"),
            Instr::LoadChar(char) => println!("LOAD_CHAR {char:?}"),
            Instr::LoadBool(bool) => println!("LOAD_BOOL: {bool}"),
            Instr::Pop => println!("POP"),
            Instr::LoadField(field) => println!("LOAD_FIELD {field}"),
            Instr::LoadBuiltinField(field) => println!("LOAD_BUILTIN_FIELD {}", field as u8),
            Instr::CallBuiltinMethod(method) => println!("CALL_BUILTIN_METHOD: {}", method as u8),
            Instr::StoreField(field) => println!("STORE_FIELD {}", field),
            Instr::LoadGlobal(global) => println!("LOAD_GLOBAL {global}"),
            Instr::LoadIntSmall(int) => println!("LOAD_INT_SMALL {int}"),
            Instr::LoadInt(int) => println!("LOAD_INT {int}"),
            Instr::LoadString { ptr, len } => {
                println!("LOAD_STR {:?}", load_str!(ptr, len))
            }
            Instr::Mod => println!("MODULO"),
            Instr::Not => println!("NOT"),
            Instr::Range => println!("RANGE"),
            Instr::RangeInclusive => println!("RANGE_INCLUSIVE"),
            Instr::Ret => println!("RET"),
            Instr::LoadVariant(ident) => {
                println!("LOAD_VARIANT {}", load_str!(ident.ptr, ident.len))
            }
        };
    }
}
