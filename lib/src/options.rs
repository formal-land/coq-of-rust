use clap::*;
use serde::{Deserialize, Serialize};

#[derive(Parser, Serialize, Deserialize)]
pub struct CoqOfRustArgs {
    /// Axiomatize the definitions
    #[arg(long)]
    axiomatize: bool,
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
    pub(crate) in_cargo: bool,
    pub(crate) axiomatize: bool,
}

impl Options {
    pub fn from_args(coq_of_rust: CoqOfRustArgs) -> Self {
        let cargo_coq_of_rust = std::env::var("CARGO_COQ_OF_RUST").is_ok();

        Options {
            in_cargo: cargo_coq_of_rust,
            axiomatize: coq_of_rust.axiomatize,
        }
    }
}
