Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Result.
  Inductive t {T E : Set} : Set :=
  | Ok : T -> t
  | Err : E -> t.
  Arguments t : clear implicits.

  Global Instance IsLink (T E : Set) `{Link T} `{Link E} : Link (t T E) := {
    Φ := Ty.apply (Ty.path "core::result::Result") [] [Φ T; Φ E];
    φ x :=
      match x with
      | Ok x => Value.StructTuple "core::result::Result::Ok" [φ x]
      | Err x => Value.StructTuple "core::result::Result::Err" [φ x]
      end;
  }.
End Result.
