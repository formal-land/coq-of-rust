use clap::*;
use serde::{Deserialize, Serialize};

/// There are no options for now.
#[derive(Parser, Serialize, Deserialize)]
pub struct CoqOfRustArgs {}

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
}

impl Options {
    pub fn from_args(_args: CoqOfRustArgs) -> Self {
        let cargo_coq_of_rust = std::env::var("CARGO_COQ_OF_RUST").is_ok();

        Options {
            in_cargo: cargo_coq_of_rust,
        }
    }
}
