Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.ops.links.arith.
Require Import ruint.links.lib.
Require Import ruint.macros.

Module Impl_Rem_for_Uint_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : Usize.t) :
    Rem.Run (Self BITS LIMBS) (Uint.t BITS LIMBS) (Uint.t BITS LIMBS).
  Admitted.
End Impl_Rem_for_Uint_Uint.
Export Impl_Rem_for_Uint_Uint.
