Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import move_sui.translations.move_binary_format.file_format.

Import Run.

Module Vec.
  Record t {A : Set} : Set := {
    value : list A;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {A : Set}, t A -> Value.t.

  Global Instance IsLink (A : Set) (_ : Link A) : Link (t A) := {
    Φ := Ty.apply (Ty.path "vec") [] [Φ A];
    φ := to_value;
  }.
End Vec.
