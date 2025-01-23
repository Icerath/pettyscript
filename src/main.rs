mod bytecode;
mod codegen;
mod intern;
mod lexer;
mod parser;
#[cfg(test)]
mod tests;
mod vm;

use clap::Parser;
use parser::parse;
use std::path::PathBuf;

#[derive(clap::Parser)]
struct Args {
    path: PathBuf,
    #[arg(short, long)]
    output_bytecode: Option<PathBuf>,
}

fn main() {
    let args = Args::parse();
    let content = std::fs::read_to_string(args.path).unwrap();
    let ast = parse(&content).unwrap();
    let bytecode = codegen::codegen(&ast);
    if let Some(path) = args.output_bytecode {
        std::fs::write(path, &bytecode).unwrap();
    }
    vm::execute_bytecode(&bytecode);
}
