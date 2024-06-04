# Proof Next

In this document we present our plans and ongoing work for our next way of doing proofs on Rust programs.

We are currently rethinking how we make proofs about Rust programs. The aim is to be able to tackle programs that are much larger than before, raising the bar from a few hundred lines of code to dozens of thousands of lines of code. From our first experiments, verifying Rust code can be particularly complex due to the use of complex abstractions such as traits, that when combined with other complexities such as memory handling can make the proofs hard to manage (too many reasoning layers).

## General idea

In order to keep the complexity of the proofs manageable, we will split things into several steps:

1. Defining the "linking" where we focus on adding back the types, and making name/trait resolution.
2. Writing simulations of the Rust code, made by hand and in idiomatic Coq, optimized for the proof.
3. Proving that the simulations are equal to the linked Rust code.

The steps 1. and 2. can be done in parallel, and the step 3. can be done after the two first steps are done. That way we split our work and can add evolutions to the two rather independently.

## 1. Linking

> Ongoing work in the pull request [#562](https://github.com/formal-land/coq-of-rust/pull/562)

The plan is to add as much automation as possible for this step, that should be rather straightforward. It might not be possible or very hard to automate everything, for example for complex types due to mutual dependencies or for complex traits, typically with a lot of associated types.

We put everything in `links` folders following the names of the original files. We define for each Rust type a corresponding Coq type with a `to_ty` and `to_value` function. We make sure that there is enough information in the `Value.t` type so that we can come back to our Coq type in a unique way. This will simplify the design of a `of_value` tactic to go from `Value.t` to our Coq type.

In particular, we add back the tags for the integer values, to distinguish between the various kinds of integers (`u8`, `i32`, ...). We also add tags for the pointers, to distinguish between the various kinds of pointers (`&`, `&mut`, ...). The tags are necessary to define the `to_ty` functions as the Rust types of the various kinds of integers and pointers are different, even if we want to represent them in the same way in Coq, and this information can be used on the Rust side to know which trait instance to call for example.

We have a monad in `links/M.v` that is similar to the monad in `M.v` used for the translation but:

- It uses typed primitives, especially for the memory primitives, that are typed instead of using `Value.t`.
- It does not have name/trait instance resolution primitives, as these are resolved in the linking step.

Because the code of the linking functions closely follows the structure of the translated code, we prefer to derive them from their proof of equivalence. There is an `evaluate` function that takes a proof of equivalence and generates a linking function from it.

## 2. Simulations

We write the simulations in the same way as before. The idea is to have idiomatic Coq code that follows the structure of the original code but is written in a way that will simplify the proofs.

We represent all the integers with `Z`. We might change a few things from the original code if that can help with the proofs, for example:

- removing immutable references when these are only used to avoid copying,
- replacing references to array items with a `Z` index in the array.

We have some primitives to represent a state monad, an error monad, or a combination of both as these are often useful.

## 3. Equivalence between the simulations and the linked Rust code

This is some work that remains to be done.

Ideally, we should be able to follow the stack discipline of Rust where values that go out-of-scope can be safely de-allocated. For example, when a function defines a local `let mut` variable but does not mutate anything else, we should be able to remove this allocation from our memory representation at the end of the function's execution. Thus this function's semantics would not show any mutation of the state, easy compositionality of the proofs.

Another optimization we can hopefully do is to have `Box` pointers that really "owns" their value, so that we can actually put their values on the stack in the Coq semantics. We might be able to totally avoid having a heap in the semantics of programs using only `&`, `&mut`, `Box`, and `Rc` pointers (we will add interior mutability later).
