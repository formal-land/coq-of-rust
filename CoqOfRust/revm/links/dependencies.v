Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.core.links.array.

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

Module Type UintSig.
  Parameter BITS : Z.
  Parameter LIMBS : Z.
End UintSig.

Module Uint (S : UintSig).
  Inductive t : Set :=
  | limbs : list Z -> t.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "ruint::Uint";
  }.

  Global Instance IsToValue : ToValue t := {
    φ '(limbs x) :=
      Value.StructRecord "ruint::Uint" [
        ("limbs", φ x)
      ];
  }.

  Module Bits.
    Inductive t : Set :=
    | make : Uint.t -> t.

    Global Instance IsToTy : ToTy t := {
      Φ := Ty.path "ruint::Bits";
    }.
  
    Global Instance IsToValue : ToValue t := {
      φ '(make x) := Value.StructTuple "ruint::Bits" [φ x]
    }.
  End Bits.

  Parameter ZERO : t.
  Parameter from : Z -> t.

  Parameter eq : t -> t -> bool.
  Parameter lt : t -> t -> bool.
  Parameter gt : t -> t -> bool.
  Parameter le : t -> t -> bool.
  Parameter ge : t -> t -> bool.

  Parameter wrapping_add : t -> t -> t.
  Parameter wrapping_mul : t -> t -> t.
  Parameter wrapping_sub : t -> t -> t.
  Parameter wrapping_div : t -> t -> t.
  Parameter wrapping_rem : t -> t -> t.
  Parameter wrapping_pow : t -> t -> t.

  Parameter add_mod : t -> t -> t -> t.
  Parameter mul_mod : t -> t -> t -> t.

  Parameter as_limbs : t -> list Z.
  Parameter bit : t -> Z -> bool.

  (* bit operations *)
  Parameter not : t -> t.
  Parameter and : t -> t -> t.
  Parameter or : t -> t -> t.
  Parameter shl : t -> Z -> t.
  Parameter shr : t -> Z -> t.
End Uint.

Module U256 <: UintSig.
  Definition BITS := 256.
  Definition LIMBS := 4.
  Include Uint.
End U256.

Module B256 := U256.Bits.
