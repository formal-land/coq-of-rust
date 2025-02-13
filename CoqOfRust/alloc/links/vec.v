Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Vec.
  Parameter t : Set -> Set -> Set.

  Parameter to_value : forall {A B : Set}, t A B -> Value.t.

  Global Instance IsLink {A B : Set} `{Link A} `{Link B} : Link (t A B) := {
    Φ := Ty.path "alloc::vec::Vec";
    φ := to_value;
  }.
End Vec.
