(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.core.fmt.
Require Import CoqOfRust.alloc.

(* TODO: Implement the following items to satisfy the dependency for e2e/env file
- [?] blocks.block_types.ExtrinsicEvents
- [?] error.dispatch_error.DispatchError
- [?] error.Error
- [?] config.Config
- [x] config.polkadot.PolkadotExtrinsicParams
- [?] config.WithExtrinsicParams
- [x] tx.signer.pair_signer.PairSigner
- [x] client.online_client.OnlineClient
- [x] utils.multi_address.MultiAddress
- [x] utils.static_type.Static
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

  Module extrinsic_params.
    (* pub struct BaseExtrinsicParams<T: Config, Tip: Debug> { /* private fields */ } *)
    Unset Primitive Projections.
    Module BaseExtrinsicParams.
      Record t (T Tip : Set) 
        `{Config.Trait T}
        `{core.Debug.Trait Tip}
      : Set := { }.
    End BaseExtrinsicParams.
    Global Set Primitive Projections.
    Definition BaseExtrinsicParams := BaseExtrinsicParams.t.
  End extrinsic_params.

  (* pub struct WithExtrinsicParams<T: Config, E: ExtrinsicParams<T::Hash>> { /* private fields */ } *)
  Unset Primitive Projections.
  Module WithExtrinsicParams.
    Record t (T E : Set) 
      `{Config.Trait T}
      (* TODO: Is this the correct way to translate the type param..? *)
      `{ExtrinsicParams.Trait T T.Hash}
    : Set := { }.
  End WithExtrinsicParams.
  Global Set Primitive Projections.
  Definition WithExtrinsicParams := WithExtrinsicParams.t.

  Module polkadot.
    (* pub struct PlainTip { /* private fields */ } *)
    Unset Primitive Projections.
    Module PlainTip.
      Record t : Set := { }.
    End PlainTip.
    Global Set Primitive Projections.
    Definition PlainTip := PlainTip.t.

    (* *******TYPE DEFS******** *)
    (* pub type PolkadotExtrinsicParams<T> = BaseExtrinsicParams<T, PlainTip>; *)
    Definition PolkadotExtrinsicParams (T : Set) : Set := extrinsic_params.BaseExtrinsicParams T PlainTip.
  End polkadot.
  
End config.

Module tx.
  (* 
  pub trait Signer<T: Config> {
      // Required methods
      fn account_id(&self) -> T::AccountId;
      fn address(&self) -> T::Address;
      fn sign(&self, signer_payload: &[u8]) -> T::Signature;
  }
  *)
  Module Signer.
    Class Trait (Self T : Set) 
      `{Config.Trait T}
    : Set := {
      account_id : ref Self -> T.AccountId;
      address : ref Self -> T.Address;
      sign : ref Self -> ref (slice u8) -> T.Signature; 
    }.
  End Signer.
  
End tx.


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

Module client.
  (* pub struct OnlineClient<T: Config> { /* private fields */ } *)
  Unset Primitive Projections.
  Module OnlineClient.
    Record t : Set := { }.
  End OnlineClient.
  Global Set Primitive Projections.
  Definition OnlineClient := OnlineClient.t.
End client.

Module utils.
  Module multi_address.
    (* 
    pub enum MultiAddress<AccountId, AccountIndex> {
        Id(AccountId),
        Index(AccountIndex),
        Raw(Vec<u8>),
        Address32([u8; 32]),
        Address20([u8; 20]),
    }
    *)
    Module MultiAddress.
      Inductive t (AccountId AccountIndex : Set) : Set := 
      | Id : AccountId -> t AccountI AccountIndex
      | Index : AccountIndex -> t AccountI AccountIndex
      | Raw : alloc.vec.Vec u8 None -> t AccountI AccountIndex
      | Address32 : slice u8 -> t AccountI AccountIndex
      | Address20 : slice u8 -> t AccountI AccountIndex
      .
    End MultiAddress.
    Definition MultiAddress := MultiAddress.t.

    (* pub struct Static<T>(pub T); *)
    Unset Primitive Projections.
    Module Static.
      Record t (T : Set) : Set := { 
        _ : T;
      }.
    End Static.
    Global Set Primitive Projections.
    Definition Static := Static.t.
  End multi_address.
End utils.


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
