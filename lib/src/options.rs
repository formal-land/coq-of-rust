use clap::*;
use serde::{Deserialize, Serialize};

#[derive(Parser, Serialize, Deserialize)]
pub struct CoqOfRustArgs {
    /// Print to a file.
    #[clap(group = "output", long, env)]
    output_file: Option<String>,
}

#[derive(Parser)]
pub struct Args {
    #[clap(flatten)]
    pub coq_of_rust: CoqOfRustArgs,
    #[clap(last = true)]
    pub rust_flags: Vec<String>,
}

#[derive(Clone)]
pub struct Options {
    pub(crate) output_file: String,
    pub(crate) in_cargo: bool,
}

impl Options {
    pub fn from_args(args: CoqOfRustArgs) -> Self {
        let cargo_coq_of_rust = std::env::var("CARGO_COQ_OF_RUST").is_ok();
        let output_file = args.output_file.unwrap_or("Crate.v".to_string());

        Options {
            output_file,
            in_cargo: cargo_coq_of_rust,
        }
    }
}
