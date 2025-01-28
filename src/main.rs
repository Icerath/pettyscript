mod builtints;
mod bytecode;
mod codegen;
mod disassemble;
mod intern;
mod lexer;
mod parser;
#[cfg(test)]
mod tests;
mod vm;

use std::path::PathBuf;

use clap::Parser;
use disassemble::disassemble;
use parser::parse;

#[derive(clap::Parser)]
struct Args {
    path: PathBuf,
    #[arg(short, long)]
    output_bytecode: Option<PathBuf>,

    #[arg(short, long)]
    disassemble: bool,
}

fn main() {
    let args = Args::parse();
    let content = std::fs::read_to_string(args.path).unwrap();
    let ast = parse(&content).unwrap();
    let bytecode = codegen::codegen(&ast);
    if let Some(path) = args.output_bytecode {
        std::fs::write(path, &bytecode).unwrap();
    }
    if args.disassemble {
        disassemble(&bytecode);
    } else {
        vm::execute_bytecode(&bytecode);
    }
}
