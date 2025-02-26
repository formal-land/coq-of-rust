Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Record t {A : Set} : Set := {
  value : list A;
}.
Arguments t : clear implicits.

Global Instance IsLink (A : Set) `{Link A} : Link (t A) := {
  Φ :=
    Ty.apply (Ty.path "slice") [] [ Φ A ];
  φ x :=
    Value.Array (List.map φ x.(value));
}.
