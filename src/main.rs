#![feature(test)]
#![feature(cell_update)]

mod ast;
mod builtints;
mod bytecode;
mod codegen;
mod compile;
mod disassemble;
mod intern;
mod lex;
mod mir;
mod parse;
#[cfg(test)]
mod tests;
mod ty;
mod vm;

pub(crate) mod prelude {
    pub use std::{collections::BTreeMap, fmt, rc::Rc};

    pub use miette::Result;
    pub use rustc_hash::{FxHashMap as HashMap, FxHashSet as HashSet};
}

use std::{path::PathBuf, time::Instant};

use clap::Parser;
use disassemble::disassemble;

#[derive(clap::Parser)]
struct Args {
    path: PathBuf,
    #[arg(short, long)]
    output_bytecode: Option<PathBuf>,
    #[arg(short, long)]
    disassemble: bool,
    #[arg(short, long)]
    verbose: bool,
}

fn main() -> miette::Result<()> {
    let args = Args::parse();
    let start = Instant::now();
    let src = std::fs::read_to_string(args.path).unwrap();
    let bytecode = compile::compile(&src)?;

    if args.verbose {
        println!("Compiled in {:?}", start.elapsed());
    }

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
