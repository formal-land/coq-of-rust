Require Import CoqOfRust.CoqOfRust.
Require Import simulations.M.
Require CoqOfRust.core.simulations.default.
Import simulations.M.Notations.

Module Result.
  Global Instance IsToValue 
      (A B : Set) (_ : ToValue A) (_ : ToValue B) :
      ToValue (A + B) := {
    Φ := Ty.apply (Ty.path "core::result::Result") [Φ A; Φ B];
    φ x :=
      match x with
      | inl x => Value.StructTuple "core::result::Result::Ok" [φ x]
      | inr e => Value.StructTuple "core::result::Result::Err" [φ e]
      end;
  }.
End Result.
