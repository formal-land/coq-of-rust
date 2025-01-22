Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Result.
  Global Instance IsLink (A B : Set) (_ : Link A) (_ : Link B) : Link (A + B) := {
    Φ := Ty.apply (Ty.path "core::result::Result") [] [Φ A; Φ B];
    φ x :=
      match x with
      | inl x => Value.StructTuple "core::result::Result::Ok" [φ x]
      | inr e => Value.StructTuple "core::result::Result::Err" [φ e]
      end;
  }.
End Result.
