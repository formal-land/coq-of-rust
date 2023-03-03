# coq-of-rust

> Formal verification for Rust 🦀 by translation to Coq 🐓

Still a work in progress!

The translation works at the level of the [HIR](https://rustc-dev-guide.rust-lang.org/hir.html) intermediate representation of Rust.

```sh
cargo run
```

To run the tests (regenerate the Coq files that are acting as a reference):

```sh
cargo run --bin coq-of-rust -- translate --path examples-from-rust-book
```

There is a bit of code taken from the [Creusot](https://github.com/xldenis/creusot) project, to make the Cargo command `coq-of-rust` and run the translation in the same context as Cargo.
