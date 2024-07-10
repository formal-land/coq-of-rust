Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.lib.

Import simulations.M.Notations.

(* TODO: Implement `Meter` trait as Coq Class *)
Module Meter.
  Class Trait (Self : Set) : Set := { }.
End Meter.
