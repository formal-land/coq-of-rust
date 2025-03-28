Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import ruint.links.lib.

(* pub struct Signed<const BITS: usize, const LIMBS: usize>(pub(crate) Uint<BITS, LIMBS>); *)
Module Signed.
  Record t {BITS LIMBS: Usize.t} : Set := {
    value : Uint.t BITS LIMBS;
  }.
  Arguments t : clear implicits.

  Parameter to_value : forall {BITS: Usize.t} {LIMBS: Usize.t}, t BITS LIMBS -> Value.t.

  Global Instance IsLink (BITS: Usize.t) (LIMBS: Usize.t): Link (t BITS LIMBS) := {
    Φ := Ty.apply (Ty.path "alloy_primitives::signed::int::Signed") [ φ BITS; φ LIMBS ] [];
    φ := to_value;
  }.
End Signed.
