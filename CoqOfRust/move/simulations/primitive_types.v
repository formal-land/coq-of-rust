Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.move.move_core_types.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.simulations.lib.

Import simulations.M.Notations.

Module U256.
  Inductive t : Set :=
  | Make (_ : Z).
End U256.
