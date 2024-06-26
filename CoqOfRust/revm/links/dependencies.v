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

Module U256.
  Definition t : Set := Z.
  Definition size : Z := 256.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "ruint::Uint";
  }.

  Global Instance IsToValue : ToValue t.
  Admitted.
End U256.

Module B256.
  Inductive t : Set :=
  | make : U256.t -> t.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "ruint::Bits";
  }.

  Global Instance IsToValue : ToValue t.
  Admitted.
End B256.
