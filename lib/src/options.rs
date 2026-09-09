use clap::*;
use serde::{Deserialize, Serialize};

#[derive(Parser, Serialize, Deserialize)]
pub struct RocqOfRustArgs {
    /// Axiomatize the definitions
    #[arg(long)]
    axiomatize: bool,
    /// Also generate a JSON output
    #[arg(long)]
    with_json: bool,
    /// Logical Rocq module prefix used by the generated runtime imports
    #[arg(long)]
    runtime_module_prefix: Option<String>,
    /// Path to a configuration file
    #[arg(long, default_value = "rocq-of-rust-config.json")]
    configuration_file: String,
    /// Generate the reoder section of configuration file in the stdout
    #[arg(long)]
    generate_reorder: bool,
}

#[derive(Parser)]
pub struct Args {
    #[clap(flatten)]
    pub rocq_of_rust: RocqOfRustArgs,
    #[clap(last = true)]
    pub rust_flags: Vec<String>,
}

#[derive(Clone)]
pub struct Options {
    pub(crate) in_cargo: bool,
    pub(crate) axiomatize: bool,
    pub(crate) with_json: bool,
    pub(crate) runtime_module_prefix: Option<String>,
}

impl Options {
    pub fn from_args(rocq_of_rust: RocqOfRustArgs) -> Self {
        let cargo_rocq_of_rust = std::env::var("CARGO_ROCQ_OF_RUST").is_ok();

        Options {
            in_cargo: cargo_rocq_of_rust,
            axiomatize: rocq_of_rust.axiomatize,
            with_json: rocq_of_rust.with_json,
            runtime_module_prefix: rocq_of_rust.runtime_module_prefix,
        }
    }
}
