use std::{fs, io, path::PathBuf};

use clap::Parser;
use formatter::Config;
use parser::parse_many;

#[derive(Parser)]
struct Args {
    path: PathBuf,
    #[arg(long, help = "fixes the file inplace")]
    fix: bool,
}

fn main() -> io::Result<()> {
    let args = Args::parse();
    let input = fs::read_to_string(&args.path)?;
    let ast = parse_many(&input).unwrap();
    let repr = formatter::format_many(&ast, Config::default());
    eprintln!("{repr}");
    if args.fix {
        fs::write(args.path, repr)?;
    }
    Ok(())
}
