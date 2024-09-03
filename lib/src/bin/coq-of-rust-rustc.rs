#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_session;

use clap::*;
use coq_of_rust_lib::{
    callbacks::*,
    options::{Args, CoqOfRustArgs, Options},
};
use rustc_driver::RunCompiler;
use std::{env, process::Command};

struct DefaultCallbacks;
impl rustc_driver::Callbacks for DefaultCallbacks {}

fn main() {
    let handler =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());

    rustc_driver::init_rustc_env_logger(&handler);
    setup_plugin();
}

fn setup_plugin() {
    let mut args = env::args().collect::<Vec<_>>();

    let is_wrapper = args.get(1).map(|s| s.contains("rustc")).unwrap_or(false);

    if is_wrapper {
        args.remove(1);
    }

    let coq_of_rust: CoqOfRustArgs = if is_wrapper {
        serde_json::from_str(&std::env::var("COQ_OF_RUST_ARGS").unwrap()).unwrap()
    } else {
        let all_args = Args::parse_from(&args);
        args = all_args.rust_flags;
        all_args.coq_of_rust
    };

    let sysroot = sysroot_path();
    args.push(format!("--sysroot={sysroot}"));

    let normal_rustc = args.iter().any(|arg| arg.starts_with("--print"));
    let primary_package = std::env::var("CARGO_PRIMARY_PACKAGE").is_ok();

    // Did the user ask to compile this crate? Either they explicitly invoked `coq_of_rust-rustc`
    // or this is a primary package.
    let user_asked_for = !is_wrapper || primary_package;

    if normal_rustc || !user_asked_for {
        return RunCompiler::new(&args, &mut DefaultCallbacks {})
            .run()
            .unwrap();
    } else {
        let opts = Options::from_args(coq_of_rust);
        let mut callbacks = ToCoq::new(opts);

        RunCompiler::new(&args, &mut callbacks).run().unwrap();
    }
}

fn sysroot_path() -> String {
    let toolchain: toml::Value = toml::from_str(include_str!("../../../rust-toolchain")).unwrap();
    let channel = toolchain["toolchain"]["channel"].as_str().unwrap();

    let output = Command::new("rustup")
        .arg("run")
        .arg(channel)
        .arg("rustc")
        .arg("--print")
        .arg("sysroot")
        .output()
        .unwrap();

    String::from_utf8(output.stdout).unwrap().trim().to_owned()
}
