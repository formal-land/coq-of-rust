Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

(* Note: here we use axioms for these definitions. We should use a standard library for these
   instead. *)
Module Map.
  Parameter t : Set -> Set -> Set.

  Parameter get : forall {K V : Set}, t K V -> K -> option V.

  Parameter keys : forall {K V : Set}, t K V -> list K.

  Parameter empty : forall {K V : Set}, t K V.
End Map.

Module Set_.
  Parameter t : Set -> Set.

  Parameter empty : forall {A : Set}, t A.

  Parameter add : forall {A : Set}, A -> t A -> t A.
End Set_.