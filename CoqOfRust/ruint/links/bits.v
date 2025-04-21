Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import ruint.links.lib.
Require Import ruint.bits.
Require Import core.ops.links.bit.


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

  Instance run_arithmetic_shr :
        forall (BITS LIMBS : Usize.t)
               (x1 : Uint.t BITS LIMBS)
               (x2 : Integer.t IntegerKind.Usize),
        Run.Trait (bits.Impl_ruint_Uint_BITS_LIMBS.arithmetic_shr (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ] (Uint.t BITS LIMBS).
  Proof.
  Admitted.
End Impl_Uint.
Export Impl_Uint.
Module Impl_Shl_for_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : Usize.t) :
    Shl.Run (Self BITS LIMBS) Usize.t (Self BITS LIMBS).
  Admitted.
End Impl_Shl_for_Uint.
Export Impl_Shl_for_Uint.
Module Impl_Shr_for_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : Usize.t) :
    Shr.Run (Self BITS LIMBS) Usize.t (Self BITS LIMBS).
  Admitted.
End Impl_Shr_for_Uint.
Export Impl_Shr_for_Uint.

