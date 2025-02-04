mod builtints;
mod bytecode;
mod codegen;
mod disassemble;
mod errors;
mod hir;
mod intern;
mod lexer;
mod parser;
#[cfg(test)]
mod tests;
mod typck;
mod vm;

use std::path::PathBuf;

use clap::Parser;
use disassemble::disassemble;
use parser::{Ast, parse};

#[derive(clap::Parser)]
struct Args {
    path: PathBuf,
    #[arg(short, long)]
    output_bytecode: Option<PathBuf>,

    #[arg(short, long)]
    disassemble: bool,
}

fn main() -> miette::Result<()> {
    let args = Args::parse();
    let src = std::fs::read_to_string(args.path).unwrap();
    let ast = parse(&src)?;
    let mut hir = hir::Lowering::new(&src);
    let block = hir.block(&ast).unwrap();
    println!("{block:?}");
    println!("{:?}", &hir.subs);

    return Ok(());

    let ast = Ast { src: &src, body: &ast };
    let bytecode = codegen::codegen(ast)?;
    if let Some(path) = args.output_bytecode {
        std::fs::write(path, &bytecode).unwrap();
    }
    if args.disassemble {
        disassemble(&bytecode);
    } else {
        // Safety: codegen must produce correct bytecode.
        unsafe { vm::execute_bytecode(&bytecode) };
    }
    Ok(())
}
