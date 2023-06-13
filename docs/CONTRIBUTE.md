# Contribute

Here we describe the architecture of the project to help contributions to the project.

## The `coq-of-rust` command

The  `coq-of-rust` command, called with `cargo coq-of-rust`, is defined in the file [bin/cargo-coq-of-rust.rs](../lib/src/bin/cargo-coq-of-rust.rs). This file is a wrapper around the library [lib.rs](../lib/src/lib.rs) that defines the translation from Rust to Coq.

We define all the translation from Rust to Coq in Rust. This has following advantages:

- we can use the API of the Rust compiler to parse Rust code
- the resulting command is easy to integrate into an existing Rust project
- anyone who already knows Rust can contribute to the project
- this forces us to practice Rust on a daily basis

The translation is done in three steps:

1. translate the HIR representation of the Rust crate/file to our Coq AST
2. apply a monadic translation to the Coq AST
3. pretty-print the Coq AST

### 1. From HIR to Coq AST

### 2. Monadic translation

We apply a monadic translation to the whole code. The type of our monad is `M A`. We use the notation `let*` for the "bind" operator, and `Pure` for "return", to distinguish them from the Rust keywords `let` and `return`. We generate temporary variables named `α1`, `α2`, etc. for intermediate results that must go through a "bind".

### 3. Pretty-printing

We use the Rust library [pretty](https://github.com/Marwes/pretty.rs) to pretty-print our Coq AST to a string with a maximum line width of 80 characters. The aim of the pretty-printing is to avoid having lines that are too long and unreadable. The whole goal is to know when to break lines and how to indent the code. We group the primitives we use from `pretty` in the [render.rs](../lib/src/render.rs) file. This helped to reduce and uniformize the size of the pretty-printing code.

## Coq libraries

In order to compile the translated Coq files, we need to define the standard library of Rust and a set of language primitives in Coq. Indeed, these are dependencies for any code that we wish to translate.

This is done in the file [CoqOfRust.v](../CoqOfRust/CoqOfRust.v). This file depends on many other files as we wanted to split the definition of the Rust standard library in many files. This is to make it easier to navigate the code and to compile it.
