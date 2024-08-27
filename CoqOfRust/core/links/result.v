Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Result.
  Global Instance IsToTy (A B : Set) (_ : ToTy A) (_ : ToTy B) : ToTy (A + B) := {
    Φ := Ty.apply (Ty.path "core::result::Result") [] [Φ A; Φ B];
  }.

  Global Instance IsToValue (A B : Set) (_ : ToValue A) (_ : ToValue B) : ToValue (A + B) := {
    φ x :=
      match x with
      | inl x => Value.StructTuple "core::result::Result::Ok" [φ x]
      | inr e => Value.StructTuple "core::result::Result::Err" [φ e]
      end;
  }.
End Result.
