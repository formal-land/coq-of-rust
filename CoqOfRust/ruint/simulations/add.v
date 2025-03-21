Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.simulations.M.
Require Import ruint.links.add.
Require Import ruint.links.lib.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run_wrapping_add Stack
      (BITS LIMBS : Usize.t)
      (x1 x2 : Self BITS LIMBS) :
    Run.Trait Stack
      (Impl_Uint.run_wrapping_add BITS LIMBS x1 x2).
  Admitted.
End Impl_Uint.
