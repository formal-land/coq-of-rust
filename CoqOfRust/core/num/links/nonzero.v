Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.num.nonzero.

(* pub struct NonZero<T: ZeroablePrimitive>(T::NonZeroInner); *)
Module NonZero.
  Record t {T : Set} : Set := {
    value : T;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink {T : Set} `{Link T} : Link (t T) := {
    Φ := Ty.path "core::num::NonZero";
    φ x :=
      Value.StructTuple "core::num::NonZero" [
        φ x.(value)
      ];
  }.
End NonZero.