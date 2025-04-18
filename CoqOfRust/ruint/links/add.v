Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.ops.links.arith.
Require Import ruint.links.lib.
Require Import ruint.add.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  (* pub const fn wrapping_add(self, rhs: Self) -> Self *)
  Instance run_wrapping_add
      (BITS LIMBS : Usize.t)
      (x1 x2 : Self BITS LIMBS) :
    Run.Trait
      (add.Impl_ruint_Uint_BITS_LIMBS.wrapping_add (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
      (Self BITS LIMBS).
  Admitted.

  (* pub const fn wrapping_neg(self) -> Self *)
  Instance run_wrapping_neg
    (BITS LIMBS : Usize.t)
    (x : Self BITS LIMBS) :
  Run.Trait
    (add.Impl_ruint_Uint_BITS_LIMBS.wrapping_neg (φ BITS) (φ LIMBS)) [] [] [ φ x ]
    (Self BITS LIMBS).
  Admitted.

  (* pub const fn wrapping_sub(self, rhs: Self) -> Self *)
  Instance run_wrapping_sub
    (BITS LIMBS : Usize.t)
    (x1 x2 : Self BITS LIMBS) :
  Run.Trait
    (add.Impl_ruint_Uint_BITS_LIMBS.wrapping_sub (φ BITS) (φ LIMBS)) [] [] [ φ x1; φ x2 ]
    (Self BITS LIMBS).
  Admitted.
End Impl_Uint.
Export Impl_Uint.

Module Impl_Add_for_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : Usize.t) :
    Add.Run (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS).
  Admitted.
End Impl_Add_for_Uint.
Export Impl_Add_for_Uint.

Module Impl_Sub_for_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : Usize.t) :
    Sub.Run (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS).
  Admitted.
End Impl_Sub_for_Uint.
Export Impl_Sub_for_Uint.
