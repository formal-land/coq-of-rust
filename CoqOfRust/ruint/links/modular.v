Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import ruint.links.lib.
Require Import ruint.modular.

(* impl<const BITS: usize, const LIMBS: usize> Uint<BITS, LIMBS> *)
Module Impl_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
      Uint.t BITS LIMBS.

  (* pub fn add_mod(self, rhs: Self, modulus: Self) -> Self *)
  Instance run_add_mod
        (BITS LIMBS : Usize.t)
        (x1 x2 : Self BITS LIMBS) :
    Run.Trait
      (modular.Impl_ruint_Uint_BITS_LIMBS.add_mod (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
      (Self BITS LIMBS).
    Admitted.

  (* pub fn mul_mod(self, rhs: Self, modulus: Self) -> Self *)
  Instance run_mul_mod
      (BITS LIMBS : Usize.t)
      (x1 x2 : Self BITS LIMBS) :
  Run.Trait
    (modular.Impl_ruint_Uint_BITS_LIMBS.mul_mod (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
    (Self BITS LIMBS).
  Admitted.

  (* pub fn pow_mod(self, exp: Self, modulus: Self) -> Self *)
  Instance run_pow_mod
      (BITS LIMBS : Usize.t)
      (x1 x2 : Self BITS LIMBS) :
  Run.Trait
    (modular.Impl_ruint_Uint_BITS_LIMBS.pow_mod (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
    (Self BITS LIMBS).
  Admitted.
End Impl_Uint.
