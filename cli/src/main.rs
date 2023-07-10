extern crate coq_of_rust_lib;

use std::path::{Path, PathBuf};

use clap::Args;
use clap::{Parser, Subcommand};

#[derive(Args)]
struct Translate {
    /// Sets a path to rust project
    #[arg(short, long, value_name = "PATH", value_parser = is_valid_path)]
    path: PathBuf,
    /// Axiomatize the definitions
    #[arg(long, value_name = "axiomatize", default_value_t = false)]
    axiomatize: bool,
}

fn is_valid_path(path: &str) -> Result<PathBuf, String> {
    let target_path = Path::new(path);
    if target_path.exists() {
        Ok(target_path.to_path_buf())
    } else {
        Err(format!("Path does not exist: {path}"))
    }
}

#[derive(Subcommand)]
enum Commands {
    /// Translate rust files to coq files
    Translate(Translate),
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,

    /// Turn debugging information on
    #[arg(short, long, action = clap::ArgAction::Count)]
    debug: u8,
}

fn main() {
    use coq_of_rust_lib::core;
    let cli = Cli::parse();

    match cli.command {
        Commands::Translate(t) => {
            println!("Translating: {}", &t.path.display());
            core::run(core::CliOptions {
                path: t.path,
                axiomatize: t.axiomatize,
            });
            println!("Finished.");
        }
    }
}
