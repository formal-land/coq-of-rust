Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Option.
  Global Instance IsToTy (A : Set) (_ : ToTy A) : ToTy (option A) := {
    Φ := Ty.apply (Ty.path "core::option::Option") [Φ A];
  }.

  Global Instance IsToValue (A : Set) (_ : ToValue A) : ToValue (option A) := {
    φ x :=
      match x with
      | None => Value.StructTuple "core::option::Option::None" []
      | Some x => Value.StructTuple "core::option::Option::Some" [φ x]
      end;
  }.
End Option.
