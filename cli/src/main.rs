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
    /// Axiomatize the definitions with everything as public
    #[arg(long, value_name = "axiomatize_public", default_value_t = false)]
    axiomatize_public: bool,
    /// Generate the "reorder" section of the configuration file
    #[arg(long, value_name = "generate_reorder", default_value_t = false)]
    generate_reorder: bool,
    /// Output path where to place the translation
    #[arg(long, value_name = "output_path", value_parser = is_valid_path, default_value = "coq_translation")]
    output_path: PathBuf,
    /// Configuration file path
    #[arg(long, value_name = "config", default_value = "coq-of-rust-config.json")]
    configuration_file: String,
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
                output: t.output_path,
                axiomatize: t.axiomatize,
                axiomatize_public: t.axiomatize_public,
                generate_reorder: t.generate_reorder,
                configuration_file: t.configuration_file,
            });
            println!("Finished.");
        }
    }
}
