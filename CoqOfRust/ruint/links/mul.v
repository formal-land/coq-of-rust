Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import ruint.links.lib.
Require Import ruint.mul.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  (* pub const fn wrapping_mul(self, rhs: Self) -> Self *)
  Instance run_wrapping_mul
      (BITS LIMBS : Usize.t)
      (x1 x2 : Self BITS LIMBS) :
    Run.Trait
      (mul.Impl_ruint_Uint_BITS_LIMBS.wrapping_mul (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
      (Self BITS LIMBS).
  Admitted.
End Impl_Uint.
