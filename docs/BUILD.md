# Installation and Build Tutorial

## Rust

### Cargo plugin

In order to install `coq-of-rust` run the following command from the
root of this repository:
```sh
cargo install --path lib/
```

This command would build and install the `coq-of-rust` library and
the cargo plugin.

Then, in any Rust project, generate a `Crate.v` file with the Coq
translation of the crate using this command:
```sh
cargo coq-of-rust
```

Sometimes the execution of the above command might result with an
error related to Rust library versions mismatch. In that case, copy
the `rust-toolchain` config file (which can be found in the root of
this repository) to the root of the Rust project you want to generate
the translation of.

### Standalone executable

Additionally, it is also possible to build `coq-of-rust` as a
standalone executable. This method has an advantage of supporting the
translation of individual files, while the cargo plugin only supports
the translation of the whole crates.

For example, the following command would build `coq-of-rust` as a
standalone executable an use it to translate one of the test examples:
```sh
cargo run --bin coq-of-rust -- translate --path examples/rust_book/hello_world/hello_world.rs
```

Note that the standalone executable and the cargo plugin versions of
`coq-of-rust` support different sets of command line options. Run
`coq-of-rust` with `--help` option to see what options are supported.

Using `coq-of-rust` as a standalone executable is intended for testing
purposes. We generally recommend to use the cargo plugin instead.

### Tests

The following command allows to regenerate the snapshots of the
translations of the test files:
```sh
python run_tests.py
```

If `coq-of-rust` would fail to translate some of the test files, it
would produce a file with an error instead.

Check if some freshly generated translation results differ to those
included in the repository:
```sh
git diff
```

## Coq

In order to install dependencies and build the Coq part of the project
run the following commands.

Create a new opam switch:
```sh
opam switch create coq-of-rust ocaml.5.1.0
```

Add the repository with Coq packages:
```sh
opam repo add coq-released https://coq.inria.fr/opam/released
```

Go to the directory with Coq files:
```sh
cd CoqOfRust
```

Install the required dependencies:
```sh
opam install --deps-only .
```

Compile the Coq files:
```sh
make
```