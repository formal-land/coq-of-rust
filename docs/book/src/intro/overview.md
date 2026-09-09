# Overview

This page provides an overview of the rocq-of-rust project and its goals.

## Project Goals

The primary goal is to enable formal verification of Rust programs by:

1. **Clean translation** - Generate Rocq code that closely resembles the original Rust
2. **Verification-friendly output** - Structure the output to facilitate proof writing
3. **Scalability** - Handle large codebases (tens of thousands of lines)
4. **Maintainability** - Keep the translator simple for long-term maintenance

## Architecture

rocq-of-rust reads Rust's HIR (High-level Intermediate Representation) from the `rustc` compiler and translates it to Rocq in a single pass.

### Rust Intermediate Representations

Rust has several intermediate languages:

| IR | Description |
|----|-------------|
| **AST** | Syntax tree from parsing |
| **HIR** | Cleaned AST with semantic information |
| **THIR** | HIR with full type information |
| **MIR** | Low-level representation |

We translate from **HIR** level. This differs from projects like Creusot which use MIR.

### Translation Pipeline

```
┌────────────────────────────────────────────────────────┐
│                    Rust Compiler                        │
│  ┌─────┐    ┌─────┐    ┌──────┐    ┌─────┐            │
│  │ AST │ -> │ HIR │ -> │ THIR │ -> │ MIR │            │
│  └─────┘    └──┬──┘    └──────┘    └─────┘            │
└───────────────┬────────────────────────────────────────┘
                │
                ▼
┌────────────────────────────────────────────────────────┐
│                   rocq-of-rust                          │
│  ┌─────────────┐    ┌─────────────┐    ┌────────────┐ │
│  │  Read HIR   │ -> │ Internal AST│ -> │ Pretty Print│ │
│  └─────────────┘    └─────────────┘    └────────────┘ │
└────────────────────────────────────────────────────────┘
                                                │
                                                ▼
                                         ┌────────────┐
                                         │  Rocq .v   │
                                         │   Files    │
                                         └────────────┘
```

## Handling Rust Features

### Mutations

One challenge is representing Rust's mutations in Rocq. Rust heavily uses mutable references (`&mut`) for performance. The type system's exclusive reference guarantee helps, but we still need careful encoding via:

- State monad for tracking mutations
- Local state that can be "forgotten" at scope exit
- Stack discipline following Rust's ownership model

### Method Overloading

Rust allows multiple `impl` blocks and trait implementations. Since Rocq doesn't support overloading, we use type classes:

```rocq
Class Method (name : string) (T : Set) : Set := {
  method : T;
}.
```

The type class inference determines which implementation to use based on the expected type `T`.

### Traits

Traits map to Rocq type classes with associated types becoming type parameters.

## Verification Workflow

The recommended approach splits verification into three steps:

1. **Linking** - Resolve types and trait instances, add back type information
2. **Simulation** - Write idiomatic Rocq models optimized for proofs
3. **Equivalence proofs** - Prove simulations match linked code

This separation enables parallel work and independent evolution of each layer.

## Related Projects

- [Creusot](https://github.com/xldenis/creusot) - Rust verification via Why3 (MIR-based)
- [Prusti](https://www.pm.inf.ethz.ch/research/prusti.html) - Rust verification via Viper
- [Kani](https://github.com/model-checking/kani) - Rust model checking
