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

Module string.
  Unset Primitive Projections.
  Module String.
    Record t : Set := { }.
  End String.
  Global Set Primitive Projections.
  Definition String := String.t.
End string.

Module collections.
  Module btree_map.
  Unset Primitive Projections.
  Module BTreeMap.
    Record t (K V A : Set) : Set := { }.
  End BTreeMap.
  Global Set Primitive Projections.
  Definition BTreeMap := BTreeMap.t.
  End btree_map.
End collections.
