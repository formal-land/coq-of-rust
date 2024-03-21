# User Tutorial

This tutorial provides some examples and tips for using `coq-of-rust`
as well as a list of supported command line options and their
description. The first part of the tutorial describes the cargo plugin
version of `coq-of-rust`, while the second part describes the
standalone executable version. Note that this two versions of
`coq-of-rust` support different sets of command line options. See our
[build tutorial](./BUILD.md) for instructions on how to build either
of those versions of `coq-of-rust`.

## Table of Contents

- [Cargo plugin](#cargo-plugin)
  - [Example](#example-0)
  - [Tips](#tips-0)
  - [Inteface](#interface-0)
- [Standalone executable](#standalone-executable)
  - [Example](#example-1)
  - [Tips](#tips-1)
  - [Inteface](#interface-1)

## Cargo plugin

### Example

In any Rust project, generate a `Crate.v` file with the Coq
translation of the crate using this command:
```sh
cargo coq-of-rust
```

### Tips

Sometimes the execution of the above command might result with an
error related to Rust library versions mismatch. In that case, copy
the `rust-toolchain` config file (which can be found in the root of
this repository) to the root of the Rust project you want to generate
the translation of.

### Interface

Usage: `cargo coq-of-rust [OPTIONS] [-- <RUST_FLAGS>...]`

Arguments:
  `[RUST_FLAGS]...`

Options:
- `--axiomatize`
  Axiomatize the definitions
- `-h`, `--help`
  Print help

## Standalone executable

### Example

The following command can be used to translate one of the
`coq-of-rust` test examples:
```sh
./coq-of-rust translate --path examples/rust_book/hello_world/hello_world.rs
```

### Tips

Using `coq-of-rust` as a standalone executable is intended for testing
purposes. We generally recommend to use the cargo plugin instead.

### Interface

Usage: `coq-of-rust [OPTIONS] <COMMAND>`

Commands:
- `translate` Translate rust files to coq files
- `help`      Print this message or the help of the given subcommand(s)

Options:
- `-d`, `--debug...` Turn debugging information on
- `-h`, `--help`     Print help
- `-V`, `--version`  Print version

#### Translate subcommand

Usage: `coq-of-rust translate [OPTIONS] --path <PATH>`

Options:
- `-p`, `--path <PATH>`           Sets a path to rust file
- `--axiomatize`                  Axiomatize the definitions
- `--output-path <output_path>`   Output path where to place the translation `[default: coq_translation]`
- `-h`, `--help`                  Print help
