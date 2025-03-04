Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.cmp.
Require Import ruint.links.lib.
Require Import ruint.cmp.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  (* pub fn is_zero(&self) -> bool *)
  Instance run_is_zero
      (BITS LIMBS : Usize.t)
      (self : Ref.t Pointer.Kind.Ref (Self BITS LIMBS)) :
    Run.Trait
      (cmp.Impl_ruint_Uint_BITS_LIMBS.is_zero (φ BITS) (φ LIMBS)) [] [] [ φ self ]
      bool.
  Admitted.
End Impl_Uint.
Export Impl_Uint.

(* impl<const BITS: usize, const LIMBS: usize> PartialOrd for Uint<BITS, LIMBS> *)
Module Impl_PartialOrd_for_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : Usize.t) : PartialOrd.Run (Self BITS LIMBS) (Self BITS LIMBS).
  Admitted.
End Impl_PartialOrd_for_Uint.
Export Impl_PartialOrd_for_Uint.
