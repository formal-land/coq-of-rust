Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import ruint.links.lib.
Require Import ruint.bytes.

Module Impl_Uint.
  (* Uint<BITS, LIMBS> *)
  Definition Self (BITS LIMBS : Usize.t) : Set :=
    Uint.t BITS LIMBS.

  (* pub const fn to_be_bytes<const BYTES: usize>(&self) -> [u8; BYTES] *)
  Instance run_to_be_bytes
      (BITS LIMBS BYTES : Usize.t)
      (x : Ref.t Pointer.Kind.Ref (Self BITS LIMBS)) :
    Run.Trait
      (bytes.Impl_ruint_Uint_BITS_LIMBS.to_be_bytes (φ BITS) (φ LIMBS)) [ φ BYTES ] [] [ φ x ]
      (array.t U8.t BYTES).
  Admitted.

  (* pub const fn from_be_bytes<const BYTES: usize>(bytes: [u8; BYTES]) -> Self *)
  Instance run_from_be_bytes
      (BITS LIMBS BYTES : Usize.t)
      (bytes : array.t U8.t BYTES) :
    Run.Trait
      (bytes.Impl_ruint_Uint_BITS_LIMBS.from_be_bytes (φ BITS) (φ LIMBS)) [ φ BYTES ] [] [ φ bytes ]
      (Self BITS LIMBS).
  Admitted.
End Impl_Uint.
Export Impl_Uint.
