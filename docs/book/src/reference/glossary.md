# Glossary

Common terms used in rocq-of-rust documentation.

## A

### Associated Type
A type defined within a trait that implementations must provide. In Rust:
```rust
trait Iterator {
    type Item;  // Associated type
}
```

## C

### Curry-Howard Correspondence
The correspondence between proofs and programs: propositions are types, proofs are programs.

## E

### EVM
Ethereum Virtual Machine. The stack-based virtual machine that executes smart contracts on Ethereum.

## F

### Formal Verification
Mathematical proof that a program satisfies its specification for all possible inputs.

## G

### Gas
Unit measuring computational cost in the EVM. Each opcode consumes a specific amount of gas.

## H

### HIR (High-level IR)
Rust's High-level Intermediate Representation. A cleaned-up AST with semantic information. rocq-of-rust translates from this level.

## I

### Inductive Type
A type defined by its constructors in Rocq:
```rocq
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.
```

## L

### Lemma
A provable statement in Rocq, typically a helper for larger theorems:
```rocq
Lemma add_comm : forall n m, n + m = m + n.
```

### Linking
The process of resolving types and trait instances in translated code, producing typed Rocq.

## M

### MIR (Mid-level IR)
Rust's low-level intermediate representation. Used by some verification tools but not rocq-of-rust.

### Monad
An abstraction for sequencing computations with effects. rocq-of-rust uses monads to model mutations, errors, etc.
```rocq
Definition M A := State -> (A * State).
```

## O

### Opcode
A single instruction in a virtual machine. EVM opcodes include ADD, PUSH, CALL, etc.

## P

### Proof Assistant
Interactive software for writing machine-checked proofs. Rocq (formerly Coq) is a proof assistant.

## R

### Rocq
The proof assistant used by rocq-of-rust. Formerly known as Coq.

### run_symbolic
Tactic that automates linking proofs by symbolically executing translated code.

## S

### Simulation
A hand-written Rocq model of Rust code optimized for proofs. Simpler than linked code but proven equivalent.

### Stack Discipline
The rule that local variables are deallocated when they go out of scope, following Rust's ownership model.

## T

### Tactic
A command in Rocq's proof language that transforms proof goals:
- `intro` - introduce hypothesis
- `apply` - apply a lemma
- `induction` - perform structural induction
- `reflexivity` - prove equality by computation

### Theorem
A major provable statement in Rocq:
```rocq
Theorem correctness : forall input,
  program input = specification input.
```

### Trait
Rust's mechanism for defining shared behavior. Maps to type classes in Rocq.
```rust
trait Clone {
    fn clone(&self) -> Self;
}
```

### Type Class
Rocq's mechanism for ad-hoc polymorphism, used to represent Rust traits:
```rocq
Class Clone (A : Type) := {
  clone : A -> A
}.
```

## U

### U256
A 256-bit unsigned integer. The native word size of the EVM.

## V

### Value.t
The universal value type in rocq-of-rust translations. All Rust values are encoded as `Value.t`.

### Verification
The process of proving program correctness. See Formal Verification.

### vm_compute
Rocq tactic that evaluates expressions using the virtual machine, much faster than `simpl`.
