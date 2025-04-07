Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import ruint.links.lib.
Require Import ruint.div.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  (* pub fn wrapping_div(self, rhs: Self) -> Self *)
  Instance run_wrapping_div
    (BITS LIMBS : Usize.t)
    (x1 x2 : Self BITS LIMBS) :
    Run.Trait
      (div.Impl_ruint_Uint_BITS_LIMBS.wrapping_div (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
      (Self BITS LIMBS).
  Admitted.

  (* pub fn wrapping_rem(self, rhs: Self) -> Self *)
  Instance run_wrapping_rem
    (BITS LIMBS : Usize.t)
    (x1 x2 : Self BITS LIMBS) :
    Run.Trait
      (div.Impl_ruint_Uint_BITS_LIMBS.wrapping_rem (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
      (Self BITS LIMBS).
  Admitted.
End Impl_Uint.
Export Impl_Uint.
