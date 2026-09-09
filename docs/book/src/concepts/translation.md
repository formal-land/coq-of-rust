# Translation: Rust to Rocq

This chapter explains how rocq-of-rust translates Rust code to Rocq.

## Design Philosophy

The translation aims for:

1. **Fidelity** - Preserve the structure of the original Rust code
2. **Simplicity** - Single-pass translation without complex transformations
3. **Stability** - Consistent variable names for reliable proof references

## The Monadic Approach

Rust has side effects (mutations, I/O, panics) that don't exist in pure functional Rocq. We encode these using a monad `M`:

```rocq
(* Simplified monad definition *)
Inductive M (A : Type) : Type :=
  | Return : A -> M A
  | Bind : forall B, M B -> (B -> M A) -> M A
  | Read : Pointer -> M Value.t
  | Write : Pointer -> Value.t -> M unit
  | Panic : string -> M A.
```

### Example: Mutation

Rust:
```rust
fn increment(x: &mut u64) {
    *x = *x + 1;
}
```

Rocq (simplified):
```rocq
Definition increment (x : Pointer) : M unit :=
  let* val := M.read x in
  M.write x (val + 1).
```

## Value Representation

All Rust values are represented uniformly as `Value.t`:

```rocq
Inductive Value.t : Type :=
  | Integer : Z -> Value.t
  | Bool : bool -> Value.t
  | Tuple : list Value.t -> Value.t
  | Struct : string -> list (string * Value.t) -> Value.t
  | Pointer : Address -> Value.t
  (* ... more constructors *)
```

This uniform representation enables:
- Generic memory operations
- Type-agnostic function signatures
- Flexible trait instance resolution

## Function Translation

### Basic Functions

Rust:
```rust
pub fn add(a: u64, b: u64) -> u64 {
    a + b
}
```

Rocq:
```rocq
Definition add (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [a; b] =>
    let* a := M.alloc a in
    let* b := M.alloc b in
    Return (M.call_closure BinOp.add [M.read a; M.read b])
  | _, _, _ => M.impossible
  end.
```

The function takes three parameters:
- `ε` - Const generic parameters (empty for this function)
- `τ` - Type parameters (empty here)
- `α` - Value arguments

### Methods and Trait Functions

Methods include `self` as the first argument. Trait methods are looked up at runtime using the `M.get_trait_method` primitive.

## Control Flow

### Conditionals

Rust:
```rust
if condition { a } else { b }
```

Rocq:
```rocq
M.if_ condition
  (fun _ => (* a branch *))
  (fun _ => (* b branch *))
```

### Loops

Loops translate to recursive tail-call functions:

Rust:
```rust
while condition {
    body
}
```

Rocq:
```rocq
Fixpoint loop (state : State) : M State :=
  let* cond := condition state in
  if cond then
    let* state' := body state in
    loop state'
  else
    Return state.
```

### Pattern Matching

Rust `match` becomes Rocq `M.match_operator`:

```rocq
M.match_operator value [
  (fun pat1 => (* branch 1 *));
  (fun pat2 => (* branch 2 *))
]
```

## Types

### Primitive Types

| Rust | Rocq |
|------|------|
| `bool` | `Ty.path "bool"` |
| `u8`...`u128` | `Ty.path "u8"` etc. |
| `i8`...`i128` | `Ty.path "i8"` etc. |
| `usize` | `Ty.path "usize"` |
| `()` | `Ty.tuple []` |

### Composite Types

| Rust | Rocq |
|------|------|
| `(A, B)` | `Ty.tuple [A; B]` |
| `&T` | `Ty.apply (Ty.path "&") [] [T]` |
| `&mut T` | `Ty.apply (Ty.path "&mut") [] [T]` |
| `[T; N]` | `Ty.apply (Ty.path "array") [N] [T]` |

### Structs and Enums

Structs become record types, enums become sum types with constructor tags.

## Traits

Traits translate to:
1. A module containing type definitions
2. Type class instances for implementations

```rust
trait Ord {
    fn cmp(&self, other: &Self) -> Ordering;
}
```

```rocq
Module Ord.
  Class Trait (Self : Ty.t) := {
    cmp : Value.t -> Value.t -> M;
  }.
End Ord.
```

## Handling Complexity

For complex code patterns, the translation may produce verbose output. The linking and simulation phases clean this up for proofs.

See [Linking](./linking.md) for how types are resolved and [Simulation](./simulation.md) for writing proof-friendly versions.
