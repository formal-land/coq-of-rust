Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module Global.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "alloc::alloc::Global";
    φ := to_value;
  }.
End Global.
