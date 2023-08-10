(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

Module vec.
  (* pub struct Vec<T, A: Allocator = Global> { /* private fields */ } *)
  Unset Primitive Projections.
  Module Vec.
    Record t (T : Set) : Set := { }.
  End Vec.
  Definition Vec := Vec.t.
  Global Set Primitive Projections.
End vec.