(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

(* 
ink\crates\prelude\src\lib.rs:
  borrow,
  boxed,
  format,
  string,
  vec,
*)

Module borrow.
End borrow.

Module boxed.
End boxed.

Module format.
End format.

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
