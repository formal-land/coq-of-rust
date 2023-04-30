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
Formal verification is essential for critical software.

The type system of Rust already offers strong guarantees to prevent common bugs that would exist in C or Python programs, for example. We still need to write tests to catch bugs that the type system cannot prevent and cannot cover all possible use cases.

With formal verification it is possible to cover all possible execution paths (code 100% bug-free!). We replace the tests by mathematical reasoning on the code. The reasoning can be made in a proof system, for example [Coq](https://coq.inria.fr/).

This tool `coq-of-rust`, by translating Rust programs to the proof system Coq, allows to mathematically and exhaustively verify Rust programs.

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
cargo run --bin coq-of-rust -- translate --path examples-from-rust-book
```

Update the snapshots of the translations of the test files, including the error messages:

```sh
python run_tests.py
```

There is a bit of code taken from the [Creusot](https://github.com/xldenis/creusot) project, to make the Cargo command `coq-of-rust` and run the translation in the same context as Cargo.

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
Open pull-requests or issues to contribute to this project. All contributions are welcome! This project is open-source under license AGPL for the Rust code (the translator) and MIT for the Coq libraries.
