use std::{fs, io, path::PathBuf};

use clap::{Parser, Subcommand};
use formatter::Config;
use parser::parse_many;
use vm::run::Vm;

#[derive(Parser)]
struct Args {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand, Clone)]
enum Command {
    Fmt { path: PathBuf },
    Run { path: PathBuf },
}

fn main() -> io::Result<()> {
    let args = Args::parse();

    match args.command {
        Command::Run { path } => {
            let input = fs::read_to_string(path)?;
            let ast = parse_many(&input).unwrap();
            let vm = Vm::new();
            vm.exec_many(&ast);
            vm.run_main();
        }
        Command::Fmt { path } => {
            let files =
                if path.is_file() {
                    vec![path]
                } else {
                    fs::read_dir(&path)?
                        .map(|entry| entry.map(|entry| entry.path()))
                        .collect::<Result<_, io::Error>>()?
                };
            for path in files {
                let input = fs::read_to_string(&path)?;
                let ast = parse_many(&input).unwrap();
                let repr = formatter::format_many(&ast, Config::default());
                fs::write(path, repr)?;
            }
        }
    }

    Ok(())
}
