Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import ruint.links.lib.
Require Import ruint.bits.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  (* pub const fn byte(&self, index: usize) -> u8 *)
  Instance run_byte
    (BITS LIMBS BYTES : Usize.t)
    (x : Ref.t Pointer.Kind.Ref (Self BITS LIMBS)) 
    (index : Usize.t) :
    Run.Trait
      (bits.Impl_ruint_Uint_BITS_LIMBS.byte (φ BITS) (φ LIMBS)) [] [] [ φ x; φ index ]
      U8.t.
  Admitted.
End Impl_Uint.