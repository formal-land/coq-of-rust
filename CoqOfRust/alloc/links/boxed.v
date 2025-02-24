Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Box.
  Record t {T A : Set} : Set := {
    value : list T;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {T A : Set}, t T A -> Value.t.

  Global Instance IsLink (T A : Set) `{Link T} `{Link A} : Link (t T A) := {
    Φ :=
      Ty.apply (Ty.path "alloc::boxed::Box") [] [ Φ T; Φ A ];
    φ := to_value;
  }.
End Box.
