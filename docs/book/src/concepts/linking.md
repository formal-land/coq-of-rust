# Linking: Type Resolution

The linking phase adds back type information and resolves names and trait instances. This transforms the untyped translated code into typed Rocq code.

## Why Linking?

The raw translation uses `Value.t` everywhere for uniformity. Linking provides:

1. **Type safety** - Typed primitives instead of generic values
2. **Name resolution** - Concrete function references instead of string lookups
3. **Trait resolution** - Specific implementations instead of dynamic dispatch
4. **Proof automation** - Structured code that `run_symbolic` can process

## The Linked Monad

Linking uses a typed monad `M` (in `links/M.v`) that differs from the translation monad:

```rocq
(* Typed memory primitives *)
Definition read {A : Type} `{Link A} (ptr : '&A) : M A := ...
Definition write {A : Type} `{Link A} (ptr : '&mut A) (value : A) : M unit := ...

(* No name/trait resolution - already resolved *)
```

## Link Type Class

Types that can be linked implement the `Link` type class:

```rocq
Class Link (A : Set) := {
  to_ty : Ty.t;
  to_value : A -> Value.t;
  of_value : Value.t -> option A;
}.
```

This provides:
- `to_ty` - The Rocq type corresponding to a Rust type
- `to_value` - Convert to untyped representation
- `of_value` - Convert from untyped representation

## Writing Link Instances

### Basic Link Definition

For the EVM's `LT` opcode:

```rocq
Instance run_lt
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t}
    `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    instructions.bitwise.lt [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Defined.
```

### Key Components

1. **Type parameters** - `{WIRE H : Set}` with `Link` instances
2. **Associated types** - `WIRE_types` with linking evidence
3. **Trait instances** - `run_InterpreterTypes_for_WIRE`
4. **Argument linking** - `φ interpreter`, `φ _host` convert to `Value.t`
5. **Result type** - The return type (`unit` here)

## The `run_symbolic` Tactic

This tactic automates most linking proofs by:

1. Symbolically executing the translated code
2. Resolving trait method calls to concrete instances
3. Matching patterns and control flow
4. Applying linking lemmas for primitives

### When `run_symbolic` Needs Help

For complex cases, you may need to:

```rocq
Proof.
  constructor.
  run_symbolic.
  (* Manual steps for tricky parts *)
  - apply some_lemma.
  - reflexivity.
Defined.
```

## File Organization

Link files follow the source structure:

```
RocqOfRust/
  revm/
    revm_interpreter/
      instructions/
        bitwise.v              # Translated Rust
        links/
          bitwise/
            lt.v               # Link for LT opcode
            gt.v               # Link for GT opcode
            ...
```

## Integer Tags

Unlike the translation which uses raw integers, linking preserves integer type tags:

```rocq
(* Translation: just Z *)
Value.Integer 42

(* Linking: tagged integers *)
Value.Integer (IntegerKind.U64, 42)
```

This enables:
- Correct trait instance selection (different `Add` for `u8` vs `u64`)
- Overflow checking at type boundaries
- Faithful representation of Rust semantics

## Pointer Tags

Similarly for pointers:

```rocq
(* Linking distinguishes reference types *)
Value.Pointer (PointerKind.Ref, addr)      (* & *)
Value.Pointer (PointerKind.MutRef, addr)   (* &mut *)
Value.Pointer (PointerKind.Box, addr)      (* Box<T> *)
```

## Automation Strategy

The project aims to automate linking as much as possible. Current status:

| Category | Automation Level |
|----------|-----------------|
| Basic types | Fully automated |
| Simple functions | Mostly automated |
| Trait methods | Requires instances |
| Complex generics | May need manual help |
| Mutual dependencies | Often manual |

## Next Steps

After linking, you write [simulations](./simulation.md) that provide idiomatic Rocq code for proofs.
