Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import ruint.links.lib.
Require Import ruint.bits.

Module Impl_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  (* pub const fn bit(&self, index: usize) -> bool *)
  Instance run_bit (BITS LIMBS : Usize.t)
      (self : Ref.t Pointer.Kind.Ref (Self BITS LIMBS))
      (index : Usize.t) :
    Run.Trait
      (bits.Impl_ruint_Uint_BITS_LIMBS.bit (φ BITS) (φ LIMBS)) [] [] [ φ self; φ index ]
      bool.
  Admitted.
End Impl_Uint.
Export Impl_Uint.
