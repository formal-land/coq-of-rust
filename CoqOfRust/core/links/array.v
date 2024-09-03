Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Array.
  Global Instance IsToTy (A : Set) (_ : ToTy A) : ToTy (list A) := {
    Φ := Ty.apply (Ty.path "array") [] [Φ A];
  }.

  Global Instance IsToValue (A : Set) (_ : ToValue A) : ToValue (list A) := {
    φ x := Value.Array (List.map φ x);
  }.
End Array.
