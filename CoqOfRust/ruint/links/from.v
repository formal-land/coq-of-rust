Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.convert.links.mod.
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
    (T : Set) `{Link T}
    (* TODO: there should also be an instance of `UintTryFrom` that we ignore for now *)
    (value : T) :
    Run.Trait
      (from.Impl_ruint_Uint_BITS_LIMBS.from (φ BITS) (φ LIMBS)) [] [ Φ T ] [ φ value ]
      (Self BITS LIMBS).
  Admitted.
End Impl_Uint.
Export Impl_Uint.
