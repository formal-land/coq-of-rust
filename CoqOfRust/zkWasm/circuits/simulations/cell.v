Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.

Require zkWasm.simulations.deps.

Import simulations.M.Notations.

(* define_cell!(AllocatedBitCell, F::one()); *)
Module AllocatedBitCell.
  Parameter t : forall (F : Set) {_ : deps.FieldExt.Trait F}, Set.
End AllocatedBitCell.

Module AllocatedU64CellWithFlagBitDyn.
  Parameter t : forall (F : Set) {_ : deps.FieldExt.Trait F}, Set.
End AllocatedU64CellWithFlagBitDyn.

Module AllocatedU64Cell.
  Parameter t : forall (F : Set) {_ : deps.FieldExt.Trait F}, Set.
End AllocatedU64Cell.

Module AllocatedCommonRangeCell.
  Parameter t : forall (F : Set) {_ : deps.FieldExt.Trait F}, Set.
End AllocatedCommonRangeCell.

Module AllocatedUnlimitedCell.
  Parameter t : forall (F : Set) {_ : deps.FieldExt.Trait F}, Set.
End AllocatedUnlimitedCell.