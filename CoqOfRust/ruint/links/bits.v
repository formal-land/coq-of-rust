Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import core.ops.links.bit.
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

  (* pub const fn byte(&self, index: usize) -> u8 *)
  Instance run_byte
    (BITS LIMBS BYTES : Usize.t)
    (x : Ref.t Pointer.Kind.Ref (Self BITS LIMBS)) 
    (index : Usize.t) :
    Run.Trait
      (bits.Impl_ruint_Uint_BITS_LIMBS.byte (φ BITS) (φ LIMBS)) [] [] [ φ x; φ index ]
      U8.t.
  Admitted.

  (* pub fn arithmetic_shr(self, rhs: usize) -> Self *)
  Instance run_arithmetic_shr
    (BITS LIMBS : Usize.t)
    (self : Self BITS LIMBS)
    (rhs : Usize.t) :
    Run.Trait
      (bits.Impl_ruint_Uint_BITS_LIMBS.arithmetic_shr (φ BITS) (φ LIMBS)) [] [] [ φ self; φ rhs ]
      (Self BITS LIMBS).
  Admitted.
End Impl_Uint.
Export Impl_Uint.

Module Impl_BitAnd_for_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : Usize.t) :
    BitAnd.Run (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS).
  Admitted.
End Impl_BitAnd_for_Uint.
Export Impl_BitAnd_for_Uint.

Module Impl_BitOr_for_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : Usize.t) :
    BitOr.Run (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS).
  Admitted.
End Impl_BitOr_for_Uint.
Export Impl_BitOr_for_Uint.

Module Impl_BitXor_for_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : Usize.t) :
    BitXor.Run (Self BITS LIMBS) (Self BITS LIMBS) (Self BITS LIMBS).
  Admitted.
End Impl_BitXor_for_Uint.
Export Impl_BitXor_for_Uint.

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

Module Impl_Not_for_Uint.
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  Instance run (BITS LIMBS : Usize.t) :
    Not.Run (Self BITS LIMBS) (Self BITS LIMBS).
  Admitted.
End Impl_Not_for_Uint.
Export Impl_Not_for_Uint.
