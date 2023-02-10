extern crate coq_of_rust_lib;

use std::path::{Path, PathBuf};

use clap::Args;
use clap::{Parser, Subcommand};

#[derive(Args)]
struct Translate {
    /// Sets a path to rust project
    #[arg(short, long, value_name = "PATH", value_parser = is_valid_path)]
    path: PathBuf,
}

fn is_valid_path(path: &str) -> Result<PathBuf, String> {
    let target_path = Path::new(path);
    if target_path.exists() {
        Ok(target_path.to_path_buf())
    } else {
        Err(format!("Path is not valid: {path}"))
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
    let cli = Cli::parse();

    match cli.debug {
        0 => (), //println!("Debug mode is off"),
        1 => println!("Debug mode is kind of on"),
        2 => println!("Debug mode is on"),
        _ => println!("Don't be crazy"),
    }

    match &cli.command {
        Commands::Translate(path) => {
            println!("Translating: {}", &path.path.display());
            coq_of_rust_lib::coq_of_rust::coq_of_rust::run(&path.path);
            println!("Finished.");
        }
    }
}
