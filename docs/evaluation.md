# Evaluation

The goal of these experiments is to run translated Rust code on concrete inputs
and compare the results with the original Rust code. There are several possible
evaluation layers.

## Generated code

The generated code has type `M` and is the closest representation to the Rust
source. Evaluating it directly would test the translation before linking. Type
resolution can be avoided, but the evaluator would still need executable
resolution for functions, associated functions, and trait methods.

The experimental evaluator in
[`translated.v`](../RocqOfRust/evaluate/translated.v) can be extracted to OCaml.
The command `make evaluate-translated-examples`, run from the `RocqOfRust`
directory, checks five generated translations. The `add_one` example evaluates
to `42` on input `41`. The `choose_and_add` example uses a generated function
table to resolve its call to `choose_u32` by name at runtime, and evaluates to
`15` on inputs `true`, `(10, 20)`, and `5`. The `evaluation_traits` example is a
dependency-free crate using generic functions and multiple trait
implementations. Its generated trait-method table records the trait type
arguments and concrete `Self` type. The example selects the `Double` and
`Triple` implementations by `Self`, and distinguishes `Convert<u32>` from
`Convert<bool>` for the same `Offset` type. Its `compute()` function evaluates
to `41`.

The `let_mut` example evaluates a mutable local variable. Allocations are kept
on the evaluator stack, and pointers record an allocation address and a path into
the stored value. A write updates the allocation, so reading the same pointer
after `x = x + 1` returns `6` rather than the original `5`.

The `ruint` evaluation runs translated arithmetic over boundary-focused inputs.
It covers `nlimbs`, `mask`, `adc`, `sbb`, `rem_up`, and all methods of the
translated `DoubleWord<u64> for u128` implementation. For `Uint<128, 2>`, it
also evaluates the main constants, construction and conversion of limbs,
immutable and mutable limb access, mutation through the returned pointer,
cloning, default construction, and equality. The extracted evaluator therefore
uses arbitrary-precision integers through Zarith rather than OCaml machine
integers.

The evaluator supports short-circuit logical operators and fuelled loops. The
current `ruint` harness supplies the focused slice-length and `Range<usize>`
runtime entries needed to exercise that control flow. Running the translated
`adc_n` loop currently exposes a separate translation issue in the tuple-place
assignment `(lhs[i], carry) = ...`: both generated tuple outputs are bound as
`lhs`, so the original slice pointer is lost before the write.

Extracted types have a structural OCaml representation for paths, tuples,
function types, applications, dynamic traits, and associated types. Type and
constant arguments are stored separately rather than encoded into one string.
Primitive integer `MIN` and `MAX` associated constants are resolved at runtime.

This experiment handles allocation, reading and writing, sub-pointers,
closure calls, function-name resolution, monomorphic trait-method resolution,
lets, tuple matching, and conditionals. The trait-method table currently covers
only non-generic implementations without trait constant arguments. Its type
comparison is supplied at extraction time. Mutation through a local variable is
supported, as are primitive integer `MIN` and `MAX` lookups. Extracted casts
currently cover unsigned integer targets. The focused `ruint` evaluation lists
only the `core` and `DoubleWord` methods it needs. The translator now generates
complete runtime tables automatically: standalone example files include the
tables at the end of the translation, while Cargo translations produce one
`rocq_of_rust_runtime.v` file for each crate. `Runtime.combine` searches a list
of these crate runtimes, so an extracted evaluator can use definitions from
several crates. When translations are installed under a logical Rocq path that
differs from the Rust crate name, `--runtime-module-prefix` sets that path for
the runtime imports. General associated-function resolution, loops, and a wider
set of mutation patterns are not handled yet.

## Linked code without mutable stack access

The evaluator in [`M.v`](../RocqOfRust/evaluate/M.v) runs the typed `LinkM`
representation produced by `links.M.evaluate`. It uses fuel for recursive calls
and currently handles the cases needed by the
[`add_one` test](../RocqOfRust/examples/default/examples/custom/evaluate/add_one.v).

This evaluator returns `Unsupported` for operations that require mutable stack
access. `Stack.t` is heterogeneous, so reading or writing a mutable reference
requires evidence that the referenced value has the expected type.

## Linked code through simulation proofs

For programs that use the stack, another direction is to derive an output
together with a proof that `SimulateM.eval_f` produces it. The Rocq `Derive`
command can introduce the output as an existential value, while repeated use of
the simulation tactic `s` can construct the execution proof and the required
stack-access evidence.

## Simulate definitions

Pure simulate definitions can already be evaluated efficiently with
`vm_compute`. This is useful for testing the functional model, while the
corresponding `_eq` lemma connects that model to the linked translation.

## Extraction

An executable Rocq evaluator or simulate definition can be extracted to OCaml.
This may provide faster execution and easier integration with an external test
runner. OCaml is also more expressive and supports side effects, which could be
used to implement name and trait resolution outside Rocq. This can be an
advantage for evaluation methods that require these resolutions, but extraction
still depends on first choosing and completing the Rocq evaluation layer.
