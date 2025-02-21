use crate::{
    bytecode::Instr,
    compile::compile,
    vm::{BytecodeHeader, BytecodeReader},
};

pub fn disassemble(bytecode: &[u8]) {
    use println as p;

    let BytecodeHeader { version, global_stack_size, str_data, instructions } =
        { BytecodeReader::new(bytecode).read_header() };

    macro_rules! load_str {
        ($ptr:expr, $len:expr) => {{
            let ptr = $ptr;
            &str_data[ptr as usize..ptr as usize + $len as usize]
        }};
    }

    p!("VERSION {version}");
    p!("LEN CONSTS {}", str_data.len());
    p!("GLOBAL_STACK_SIZE {global_stack_size}");
    p!();

    let size_std = sizeof_std() as u32;
    let instructions = &instructions[size_std as usize..];
    let mut head = 0;

    while head < instructions.len() {
        let op = Instr::bc_read(&instructions[head..]);
        print!("{head}: ");
        head += 1 + op.size();
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
            Instr::Jump(label) => p!("JUMP {}", label - size_std),
            Instr::CJump(label) => p!("CJUMP {}", label - size_std),
            Instr::CreateFunction { stack_size } => p!("CREATE_FUNCTION {stack_size}"),
            Instr::CreateStruct { size } => p!("EMPTY_STRUCT {size}"),
            Instr::FnCall => p!("FN_CALL"),
            Instr::IterRange => p!("ITER_RANGE"),
            Instr::LoadGlobal(global) => p!("LOAD_GLOBAL {global}"),
            Instr::Load(ident) => p!("LOAD {ident}"),
            Instr::StoreGlobal(global) => p!("STORE_GLOBAL {global}"),
            Instr::Store(ident) => p!("STORE {ident}"),
            Instr::LoadChar(char) => p!("LOAD_CHAR {char:?}"),
            Instr::LoadBool(bool) => p!("LOAD_BOOL: {bool}"),
            Instr::Pop => p!("POP"),
            Instr::LoadField(field) => p!("LOAD_FIELD {field}"),
            Instr::CallBuiltinMethod(method) => p!("CALL_BUILTIN_METHOD: {}", method as u8),
            Instr::StoreField(field) => p!("STORE_FIELD {field}"),
            Instr::LoadIntSmall(int) => p!("LOAD_INT_SMALL {int}"),
            Instr::LoadInt(int) => p!("LOAD_INT {int}"),
            Instr::LoadString(str) => p!("LOAD_STR {:?}", load_str!(str.ptr, str.len)),
            Instr::Mod => p!("MODULO"),
            Instr::Not => p!("NOT"),
            Instr::Range => p!("RANGE"),
            Instr::RangeInclusive => p!("RANGE_INCLUSIVE"),
            Instr::Ret => p!("RET"),
            Instr::LoadVariant { tag } => p!("LOAD_VARIANT {tag}"),
        }
    }
}

fn sizeof_std() -> usize {
    let std = compile("").expect("std lib should compile");
    BytecodeReader::new(&std).read_header().instructions.len()
}
