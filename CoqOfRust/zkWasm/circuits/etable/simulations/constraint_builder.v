Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Require zkWasm.simulations.deps.

Import simulations.M.Notations.

Module ConstraintBuilder.
  Parameter t : forall (F : Set) {_ : deps.FieldExt.Trait F}, Set.
End ConstraintBuilder.
