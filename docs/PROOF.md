# Proof

In this guide, we present how to prove Rust programs translated in Coq by `coq-of-rust`. These are a list of recipes and conventions that are useful for us, but this may evolve in the future as we gain more experience. Do not hesitate to propose changes or improvements, and to update this document accordingly.

## Simulations

The first step is to rewrite the generated Coq code, that is something around five times larger than the original Rust code, to an idiomatic Coq version called a simulation. This step is there to make the proof manageable. The simulation should have around the same size as the original Rust code. We should not use the dependent types to write the simulations as this makes the code more complex.

We organize our developments as follows:

- `source_file.v`: the translation of some Rust source file `source_file.rs` to Coq
- `simulations/source_file.v`: the simulation of `source_file.v`
- `proofs/source_file.v`: the proof of `source_file.v` using the simulation in `simulations/source_file.v`

That way we separate the computational part from the proof part.

In the file [CoqOfRust/simulations/M.v](/CoqOfRust/simulations/M.v) we define the monads:

- `Error`
- `StateError`

with corresponding notations. These can be useful to write the simulations with the error or the state effect.

## Injections φ and Φ

We define the class `ToValue` as:

```coq
Class ToValue (A : Set) : Set := {
  Φ : Ty.t;
  φ : A -> Value.t;
}.
Arguments Φ _ {_}.
```

This states how to go from a type `A` used in the simulation to a value of type `Value.t` in the translated Rust code. It also states the type `Φ` representing the type of `A`.

This conversion is necessary, as in the translated Rust code all the types of values are collapsed in a single type `Value.t`. When writing our statements to say that our simulations are equal to the original Rust code, we always convert from the simulations values to untyped values using the projection `φ`.

Having a typeclass is useful to avoid having to precise which conversion we use when calling the projection `φ`. The downside is that we have to make sure that these conversions are unique, and create one different Coq type for each Rust type to avoid confusion.

We also add the definition for `ToValue` in the `simulations/` folders.

## Equality of the simulations

Once we have defined our simulations, we need to make sure that they behave as the original translated code. This is especially important as the original Rust code may evolve, and we need a reliable way to know what simulations should be changed.

In [CoqOfRust/proofs/M.v](/CoqOfRust/proofs/M.v) we have a predicate to express that, is a certain environment `env` and from an initial state `state`, the translated code `e` is evaluated to the value `v` and returns the new state `state'`:

```coq
{{ env , state | e ⇓ v | state' }}
```

The expression `e` is the translated Rust code, and the value `v` the simulation. Because we generally reason about a function `f` applied to several arguments `x1`, ..., `xn` and need to use the projection `φ` to convert the simulated values, we generally express the equality of the simulations as follows:

```coq
forall x1 ... xn,
{{ env , state | f (φ x1) ... (φ xn) ⇓ φ (simu_f x1 ... xn) | state' }}
```

For the common case of stateless functions, we can simplify this to:

```coq
Run.pure (f (φ x1) ... (φ xn)) (φ (simu_f x1 ... xn))
```

that is equivalent to:

```coq
forall env state,
{{ env , state | f (φ x1) ... (φ xn) ⇓ φ (simu_f x1 ... xn) | state }}
```

To simplify the verification process, it is better if the Rust code is written in a stateless style, using only immutable data structures. This way, we can totally avoid reasoning about the state of the program.

To state the equality of the simulation we can use:

- the tactic `run_symbolic` that simplifies common cases
- explicit calls to the constructors of the inductive `proofs.M.Run.t`

Showing that a simulation is equal is not obvious, and we need to make a few choices in this proof. In particular:

- We have to find, in the generated Coq code, the name for the functions, associated functions or trait instances that are called in the Rust code (the name resolution is done at this point).
- We have to decide how to allocate the memory.

## Allocation of the memory

In order to simplify the proofs, we have a choice in the way we allocate it. The default choice would be to use an infinite array, where the memory addresses are indexes in this array. But this does not give much structure for the proofs.

Instead we can provide our own memory when defining the simulations. See the trait `proofs.M.State.Trait` for that. The memory will typically be a record of options of `Value.t`, where each field of the record is what we are planning to allocate. The memory may also contain a list when the number of allocations is not statically known.

When verifying the equality of a simulation, we have a choice to make when allocating a new value (the `M.alloc` call):

- The first choice is to use an immutable value with `Run.CallPrimitiveStateAllocImmediate`. In that case the address of the value is the value itself. We can later read it but we will be stuck in the proof if we attempt to write in it. This is the preferred choice for values that we will not modify, and this should be the case of most intermediate Rust values.
- The second choice is to use a mutable value with `Run.CallPrimitiveStateAllocMutable`. In that case, the address of the value is the address of the value in the memory. We can later read and write in it. This is required for values that we will modify, for example values declared with `let mut` or using interior mutability.
