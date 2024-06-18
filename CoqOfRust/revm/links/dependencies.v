Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

(*
  /// Wrapper type around [`bytes::Bytes`] to support "0x" prefixed hex strings.
  #[derive(Clone, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
  #[repr(transparent)]
  pub struct Bytes(pub bytes::Bytes);
*)

Module Bytes.
  Parameter t : Set.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "bytes::bytes::Bytes";
  }.

  Global Instance IsToValue : ToValue t.
  Admitted.
End Bytes.

Module Address.
  Parameter t : Set.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "alloy_primitives::bits::address::Address";
  }.

  Global Instance IsToValue : ToValue t.
  Admitted.
End Address.

Module FixedBytes.
  Parameter t : Set.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "alloy_primitives::bits::fixed::FixedBytes";
  }.

  Global Instance IsToValue : ToValue t.
  Admitted.
End FixedBytes.

Definition B256 := FixedBytes.t.
Definition U256 := FixedBytes.t.

Module U256.
  Parameter ZERO : U256.
  Parameter eq : U256 -> U256 -> bool.

  Parameter wrapping_add :  U256 -> U256 -> U256.
  Parameter wrapping_mul :  U256 -> U256 -> U256.
  Parameter wrapping_sub :  U256 -> U256 -> U256.
  Parameter wrapping_div :  U256 -> U256 -> U256.
  Parameter wrapping_rem :  U256 -> U256 -> U256.
  Parameter wrapping_pow :  U256 -> U256 -> U256.

  Parameter add_mod :  U256 -> U256 -> U256 -> U256.
  Parameter mul_mod :  U256 -> U256 -> U256 -> U256.
End U256.
