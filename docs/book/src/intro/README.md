# rocq-of-rust

<div class="logo-container">
    <img src="https://raw.githubusercontent.com/formal-land/rocq-of-rust/main/logo.png" alt="rocq-of-rust logo" style="max-width: 200px;">
</div>

> **Formal verification of Rust programs using the Rocq proof assistant**

`rocq-of-rust` translates Rust code to Rocq (formerly Coq), enabling you to write mathematical proofs about your Rust programs. This provides the highest level of assurance that your code is correct.

## Why Formal Verification?

Traditional testing can only check a finite number of cases. Formal verification proves properties hold for *all* possible inputs. This is crucial for:

- **Smart contracts** handling billions in assets
- **Cryptographic implementations** requiring mathematical correctness
- **Safety-critical systems** where bugs have severe consequences
- **Protocol implementations** needing precise specification adherence

## How It Works

```
┌──────────┐     ┌─────────────┐     ┌───────────┐     ┌────────┐
│  Rust    │ ──► │   rocq-of   │ ──► │   Rocq    │ ──► │ Proofs │
│  Source  │     │    rust     │     │   Code    │     │        │
└──────────┘     └─────────────┘     └───────────┘     └────────┘
```

1. **Translation**: Rust source code is translated to Rocq
2. **Linking**: Types and trait instances are resolved
3. **Simulation**: Idiomatic Rocq models are written for verification
4. **Proofs**: Mathematical proofs establish correctness

## Key Features

- **Full Rust support**: Handles complex features including traits, generics, and lifetimes
- **Modular proofs**: Separation of linking and simulation enables scalable verification
- **EVM verification**: Active project verifying the Ethereum Virtual Machine implementation
- **Automation**: `run_symbolic` tactic automates routine linking proofs

## Quick Example

Rust code:
```rust
pub fn add(a: u64, b: u64) -> u64 {
    a + b
}
```

Translates to Rocq (simplified):
```rocq
Definition add (a b : u64) : M u64 :=
  let result := a + b in
  return result.
```

Then we can prove properties like commutativity:
```rocq
Lemma add_comm : forall a b,
  add a b = add b a.
Proof.
  intros. unfold add. lia.
Qed.
```

## Get Started

- [**Installation**](./guide/installation.md) - Set up rocq-of-rust
- [**Quick Start**](./guide/usage.md) - Translate your first Rust program
- [**Core Concepts**](./concepts/translation.md) - Understand the translation process
- [**EVM Explorer**](./evm/explorer.md) - See verified EVM opcodes in action
