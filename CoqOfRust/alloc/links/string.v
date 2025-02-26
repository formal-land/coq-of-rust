Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Module String.
  Parameter t : Set.

  Parameter to_value : t -> Value.t.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "alloc::alloc::String";
    φ := to_value;
  }.
End String.
