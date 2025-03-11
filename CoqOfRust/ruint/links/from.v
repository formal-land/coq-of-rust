Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import ruint.links.lib.
Require Import ruint.from.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  (* 
  pub fn from<T>(value: T) -> Self
        where
            Self: UintTryFrom<T>,
  *)
  Instance run_from
    (BITS LIMBS : Usize.t)
    (x1 x2 : Self BITS LIMBS) :
    Run.Trait
      (from.Impl_ruint_Uint_BITS_LIMBS.from (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
      (Self BITS LIMBS).
  Admitted.
End Impl_Uint.
