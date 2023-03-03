use clap::*;
use coq_of_rust_lib::options::Args;
use std::{
    env,
    process::{exit, Command},
};

fn main() {
    let args = Args::parse_from(std::env::args().skip(1));

    let creusot_rustc_path = std::env::current_exe()
        .expect("current executable path invalid")
        .with_file_name("coq-of-rust-rustc");

    let cargo_path = env::var("CARGO_PATH").unwrap_or_else(|_| "cargo".to_string());
    let cargo_cmd = if std::env::var_os("COQ_OF_RUST_CONTINUE").is_some() {
        "build"
    } else {
        "check"
    };
    let mut cmd = Command::new(cargo_path);
    cmd.arg(cargo_cmd)
        .args(args.rust_flags)
        .env("RUSTC_WRAPPER", creusot_rustc_path)
        .env("CARGO_COQ_OF_RUST", "1");

    cmd.env(
        "COQ_OF_RUST_ARGS",
        serde_json::to_string(&args.coq_of_rust).unwrap(),
    );

    let exit_status = cmd.status().expect("could not run cargo");
    if !exit_status.success() {
        exit(exit_status.code().unwrap_or(-1));
    }
}
