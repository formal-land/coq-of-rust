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

See the `coq-of-rust` [user guide](./GUIDE.md) for more details about
using `coq-of-rust`.

### Standalone executable

Additionally, it is also possible to build `coq-of-rust` as a
standalone executable. This method has an advantage of supporting the
translation of individual files, while the cargo plugin only supports
the translation of the whole crates.

The following command would build `coq-of-rust` as a standalone
executable (in release mode):
```sh
cargo build --bin coq-of-rust --release
```

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