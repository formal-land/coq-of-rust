(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

(* TODO: Implement the following items to satisfy the dependency for e2e/env file
- [?] blocks.block_types.ExtrinsicEvents
- [?] error.dispatch_error.DispatchError
- [?] error.Error
- [?] config.Config
- [ ] config.polkadot.PolkadotExtrinsicParams
- [ ] config.WithExtrinsicParams
- [ ] tx.signer.pair_signer.PairSigner
- [ ] client.online_client.OnlineClient
- [ ] utils.multi_address.MultiAddress
- [ ] utils.static_type.Static
*)

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
    Class Trait (Self : Set)
                {Index
                Hash
                AccountId
                Address
                Signature
                Hasher
                Header
                ExtrinsicParams
                : Set} 
    : Set := {
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

Module error.
  (* 
  pub enum Error {
      Io(Error),
      Codec(Error),
      Rpc(RpcError),
      Serialization(Error),
      Metadata(MetadataError),
      MetadataDecoding(MetadataTryFromError),
      Runtime(DispatchError),
      Decode(DecodeError),
      Encode(EncodeError),
      Transaction(TransactionError),
      Block(BlockError),
      StorageAddress(StorageAddressError),
      Unknown(Vec<u8>),
      Other(String),
  }
  *)
  (* NOTE: Current stub for Error. The `Error`s in the parameters come from varied other crates. *)
  Module Error.
    Inductive t : Set := 
    | Io
    | Codec
    | Rpc
    | Serialization
    | Metadata
    | MetadataDecoding
    | Runtime
    | Decode
    | Encode
    | Transaction
    | Block
    | StorageAddress
    | Unknown
    | Other
    .
  End Error.
  Definition Error := Error.t.

  (* NOTE: Stub for DispatchError *)
  (* 
  pub enum DispatchError {
      Other,
      CannotLookup,
      BadOrigin,
      Module(ModuleError),
      ConsumerRemaining,
      NoProviders,
      TooManyConsumers,
      Token(TokenError),
      Arithmetic(ArithmeticError),
      Transactional(TransactionalError),
      Exhausted,
      Corruption,
      Unavailable,
  }
  *)
  Module Dispatch_error.
    Inductive t : Set := 
    | Other
    | CannotLookup
    | BadOrigin
    | Module
    | ConsumerRemaining
    | NoProviders
    | TooManyConsumers
    | Token
    | Arithmetic
    | Transactional
    | Exhausted
    | Corruption
    | Unavailable
    .
  End Dispatch_error.
  Definition Dispatch_error := Dispatch_error.t.
  
  
End error.


(* NOTE: content in this module does not match its document specification *)
(* For now we follow the style in the source code *)
Module blocks.
  (* pub struct ExtrinsicEvents<T: Config> { /* private fields */ } *)
  Module block_types.
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
