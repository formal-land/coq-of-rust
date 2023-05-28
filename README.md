# <img src="logo.png" alt= "logo" width="120px" height="120px" style="vertical-align: middle;"> <span style="vertical-align: middle;">coq-of-rust</span>

> Formal verification for Rust 🦀 by translation to the proof system Coq 🐓

*⚠️ Still a work in progress! ⚠️*

## Table of Contents

- [Rationale](#rationale)
- [Prerequisites](#prerequisites)
- [Details](#details)
- [Features](#features)
- [Limitations](#limitations)
- [Alternative Projects](#alternative-projects)
- [Contributing](#contributing)

## Rationale
Formal verification allows to prevent all bugs in critical software. This is used in aerospace industry for example 🧑‍🚀.

The type system of Rust already offers strong guarantees to avoid bugs that exist in C or Python. We still need to write tests to verify the business rules or the absence of `panic`. Testing is incomplete as it cannot cover all execution cases.

With formal verification we cover all cases (code 100% bug-free!). We replace the tests by mathematical reasoning on code. You can view it as an extension of the type system, but without restrictions on the expressivity.

This tool `coq-of-rust` translates Rust programs to the formal verification language Coq to make Rust programs 100% safe 🌙.

## Prerequisites

- Rust (latest stable version)
- Coq (version 8.14 or newer)

## Details
The translation works at the level of the [HIR](https://rustc-dev-guide.rust-lang.org/hir.html) intermediate representation of Rust.

From the root of this repository, run:

```sh
cargo install --path lib/
```

Then in any Rust project, to generate a `Crate.v` file with the Coq translation of the crate:

```sh
cargo coq-of-rust
```

Translate the test files (but show the error/warning messages):

```sh
cargo run --bin coq-of-rust -- translate --path examples
```

Update the snapshots of the translations of the test files, including the error messages:

```sh
python run_tests.py
```

Compile the Coq files:

```sh
cd CoqOfRust
./configure.sh
make
```

## Features
Note that we are still developing support for most of language constructs of Rust.

- translation of a single Rust file to Coq
- translation of a whole crate project

## Limitations
This project is still early stage. We focus for now on the translation of a purely functional subset of Rust, and then will add a monadic system to support memory mutations.

## Alternative Projects

Here are other projects working on formal verification for Rust:

- [Aeneas](https://github.com/AeneasVerif/aeneas): Translation from MIR to purely functional Coq/F* code
- [Hacspec v2](https://github.com/hacspec/hacspec-v2): Translation from THIR to Coq/F* code
- [Creusot](https://github.com/xldenis/creusot): Translation from MIR to Why3 (and then SMT solvers)
- [Kani](https://github.com/model-checking/kani): Model-checking with [CBMC](https://github.com/diffblue/cbmc)

## Contributing
Open pull-requests or issues to contribute to this project. All contributions are welcome! This project is open-source under license AGPL for the Rust code (the translator) and MIT for the Coq libraries. There is a bit of code taken from the [Creusot](https://github.com/xldenis/creusot) project, to make the Cargo command `coq-of-rust` and run the translation in the same context as Cargo.
