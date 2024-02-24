use std::{fs, path::PathBuf, process::ExitCode};

use clap::Parser;
use parser::parse_many;

#[derive(Parser)]
struct Args {
    path: PathBuf,
}

fn main() -> ExitCode {
    let args = Args::parse();
    let Ok(input) = fs::read_to_string(&args.path) else {
        eprintln!("ERROR: Failed to read {:?}", args.path);
        return ExitCode::FAILURE;
    };
    let ast = parse_many(&input);
    eprintln!("{ast:?}");
    ExitCode::SUCCESS
}
