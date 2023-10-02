(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

(* pub struct Weight { /* private fields */ } *)
Unset Primitive Projections.
Module Weight.
  Record t : Set := { }.
End Weight.
Global Set Primitive Projections.
Definition Weight := Weight.t.

Module weight_v2.
  Parameter Weight : Set.
End weight_v2.
