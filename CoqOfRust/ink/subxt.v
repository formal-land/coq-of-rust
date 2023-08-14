(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

(* 
pub trait Config: 'static {
    type Index: Debug + Copy + DeserializeOwned + Into<u64>;
    type Hash: Debug + Copy + Send + Sync + Decode + AsRef<[u8]> + Serialize + DeserializeOwned + Encode + PartialEq;
    type AccountId: Debug + Clone + Serialize;
    type Address: Debug + Encode + From<Self::AccountId>;
    type Signature: Debug + Encode;
    type Hasher: Debug + Hasher<Output = Self::Hash>;
    type Header: Debug + Header<Hasher = Self::Hasher> + Send + DeserializeOwned;
    type ExtrinsicParams: ExtrinsicParams<Self::Index, Self::Hash>;
}
*)
Module config.
  Module Config.
    Class Trait (Self 
                Index
                Hash
                AccountId
                Address
                Signature
                Hasher
                Header
                ExtrinsicParams
    : Set) : Set := {
    (* NOTE: we make a very rough translation here... *)
        Index := Index;
        Hash := Hash;
        AccountId := AccountId;
        Address := Address;
        Signature := Signature;
        Hasher := Hasher;
        Header := Header;
        ExtrinsicParams := ExtrinsicParams;
    }.
  End Config.
End config.

(* NOTE: content in this module does not match its document specification *)
(* For now we follow the style in the source code *)
Module blocks.
  (* NOTE: block_types does not appear in api doc *)
  Module block_types.
    (* pub struct ExtrinsicEvents<T: Config> { /* private fields */ } *)
    Unset Primitive Projections.
    Module ExtrinsicEvents.
      Record t (T : Set) 
        `{subxt.config.Config.Trait T}
      : Set := { }.
    End ExtrinsicEvents.
    Global Set Primitive Projections.
    Definition ExtrinsicEvents := ExtrinsicEvents.t.
  End block_types.
End blocks.
