use crate::{
    bytecode::{Instr, VERSION},
    compile::compile,
    vm::BytecodeReader,
};

pub fn disassemble(bytecode: &[u8]) {
    use println as p;

    let mut reader = BytecodeReader::new(bytecode);
    let version = u32::from_le_bytes(*reader.read::<4>());
    let global_stack_size = u32::from_le_bytes(*reader.read::<4>());
    assert_eq!(version, VERSION);
    let len_consts = u32::from_le_bytes(*reader.read::<4>()) as usize;
    reader.bytes = &reader.bytes[reader.head..];
    reader.head = 0;
    let consts = std::str::from_utf8(&reader.bytes[..len_consts]).unwrap();
    reader.bytes = &reader.bytes[len_consts..];

    macro_rules! load_str {
        ($ptr:expr, $len:expr) => {{
            let ptr = $ptr;
            &consts[ptr as usize..ptr as usize + $len as usize]
        }};
    }

    println!("VERSION {version}");
    println!("LEN CONSTS {len_consts}");
    println!("GLOBAL_STACK_SIZE {global_stack_size}");
    println!();

    let size_std = sizeof_std();
    reader.head += size_std;

    while reader.head < reader.bytes.len() {
        let offset = reader.head - size_std;
        let op = Instr::bc_read(&reader.bytes[reader.head..]);
        reader.head += 1 + op.size();
        print!("{offset}: ");
        match op {
            Instr::EnumTag => p!("ENUM_TAG"),
            Instr::Abort => p!("ABORT"),
            Instr::BuildFstr { num_segments } => p!("BUILD_FSTR {num_segments:?}"),
            Instr::AddInt => p!("ADD_INT"),
            Instr::SubInt => p!("SUB_INT"),
            Instr::MulInt => p!("MUL_INT"),
            Instr::DivInt => p!("DIV_INT"),
            Instr::Neg => p!("NEG"),
            Instr::CreateMap { num_keys } => p!("CREATE_MAP {num_keys}"),
            Instr::CreateArray { size } => p!("CREATE_ARRAY {size}"),
            Instr::ArrayConcatStack => p!("ARRAY_CONCAT_STACK"),
            Instr::Dup => p!("DUP"),
            Instr::Eq => p!("EQ"),
            Instr::Less => p!("LESS"),
            Instr::Greater => p!("GREATER"),
            Instr::ArrayIndex => p!("ARRAY_INDEX"),
            Instr::StringIndex => p!("STRING_INDEX"),
            Instr::StringSliceRange => p!("STRING_SLICE_RANGE"),
            Instr::Jump(label) => p!("JUMP {label}"),
            Instr::CJump(label) => p!("CJUMP {label}"),
            Instr::CreateFunction { stack_size } => p!("CREATE_FUNCTION {stack_size}"),
            Instr::CreateStruct { size } => p!("EMPTY_STRUCT {size}"),
            Instr::FnCall => p!("FN_CALL"),
            Instr::IterRange => p!("ITER_RANGE"),
            Instr::Load(ident) => p!("LOAD {ident}"),
            Instr::Store(ident) => p!("STORE {ident}"),
            Instr::LoadChar(char) => p!("LOAD_CHAR {char:?}"),
            Instr::LoadBool(bool) => p!("LOAD_BOOL: {bool}"),
            Instr::Pop => p!("POP"),
            Instr::LoadField(field) => p!("LOAD_FIELD {field}"),
            Instr::CallBuiltinMethod(method) => p!("CALL_BUILTIN_METHOD: {}", method as u8),
            Instr::StoreField(field) => p!("STORE_FIELD {field}"),
            Instr::LoadGlobal(global) => p!("LOAD_GLOBAL {global}"),
            Instr::LoadIntSmall(int) => p!("LOAD_INT_SMALL {int}"),
            Instr::LoadInt(int) => p!("LOAD_INT {int}"),
            Instr::LoadString(str) => p!("LOAD_STR {:?}", load_str!(str.ptr, str.len)),
            Instr::Mod => p!("MODULO"),
            Instr::Not => p!("NOT"),
            Instr::Range => p!("RANGE"),
            Instr::RangeInclusive => p!("RANGE_INCLUSIVE"),
            Instr::Ret => p!("RET"),
            Instr::LoadVariant { tag } => p!("LOAD_VARIANT {tag}"),
        };
    }
}

fn sizeof_std() -> usize {
    // TODO: dedup header parsing.
    let std = compile("").expect("std lib should compile");
    let mut reader = BytecodeReader::new(&std);
    let _version = u32::from_le_bytes(*reader.read::<4>());
    let _global_stack_size = u32::from_le_bytes(*reader.read::<4>());
    let len_consts = u32::from_le_bytes(*reader.read::<4>()) as usize;
    reader.bytes = &reader.bytes[reader.head..];
    reader.head = 0;
    reader.bytes = &reader.bytes[len_consts..];
    reader.bytes.len()
}
