(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

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
    Class Trait (Self : Set) : Type := {
    (* NOTE: we make a very rough translation here... *)
        Index : Set;
        Hash : Set;
        AccountId : Set;
        Address : Set;
        Signature : Set;
        Hasher : Set;
        Header : Set;
        ExtrinsicParams : Set;
    }.

    Global Instance Type_Hash (Self : Set) `(Trait Self)
      : Notation.DoubleColonType Self "Hash" := {
      Notation.double_colon_type := Hash;
    }.
    Global Instance Type_AccountId (Self : Set) `(Trait Self)
      : Notation.DoubleColonType Self "AccountId" := {
      Notation.double_colon_type := Hash;
    }.
    Global Instance Type_Address (Self : Set) `(Trait Self)
      : Notation.DoubleColonType Self "Address" := {
      Notation.double_colon_type := Hash;
    }.
    Global Instance Type_Signature (Self : Set) `(Trait Self)
      : Notation.DoubleColonType Self "Signature" := {
      Notation.double_colon_type := Hash;
    }.
  End Config.

  Module extrinsic_params.
    (* pub struct BaseExtrinsicParams<T: Config, Tip: Debug> { /* private fields */ } *)
    Unset Primitive Projections.
    Module BaseExtrinsicParams.
      Record t (T Tip : Set) 
        `{Config.Trait T}
        `{core.fmt.Debug.Trait Tip}
      : Set := { }.
    End BaseExtrinsicParams.
    Global Set Primitive Projections.
    Definition BaseExtrinsicParams
      (T Tip : Set)
      `{Config.Trait T}
      `{core.fmt.Debug.Trait Tip}
      := BaseExtrinsicParams.t T Tip.

    (*
    pub trait ExtrinsicParams<Hash>: Debug + 'static {
    type OtherParams;

    // Required methods
    fn new(
        spec_version: u32,
        tx_version: u32,
        nonce: u64,
        genesis_hash: Hash,
        other_params: Self::OtherParams
    ) -> Self;
    fn encode_extra_to(&self, v: &mut Vec<u8>);
    fn encode_additional_to(&self, v: &mut Vec<u8>);
    }
    *)
    Module ExtrinsicParams.
      Class Trait (Self : Set) `{core.fmt.Debug.Trait Self} (Hash : Set)
        : Type := {
        OtherParams : Set;

        new : u32 -> u32 -> u64 -> Hash -> OtherParams -> Self;
        encode_extra_to :
          ref Self -> mut_ref (alloc.vec.Vec u8 alloc.vec.Vec.Default.A);
        encode_additional_to :
          ref Self -> mut_ref (alloc.vec.Vec u8 alloc.vec.Vec.Default.A);
        }.
    End ExtrinsicParams.
  End extrinsic_params.

  (* pub struct WithExtrinsicParams<T: Config, E: ExtrinsicParams<T::Hash>> { /* private fields */ } *)
  Unset Primitive Projections.
  Module WithExtrinsicParams.
    Record t (T E : Set) 
      `{Config.Trait T}
      (* TODO: Is this the correct way to translate the type param..? *)
      `{extrinsic_params.ExtrinsicParams.Trait T T::type["Hash"]}
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

    Module Impl_Debug_for_PlainTip.
      Global Instance I : core.fmt.Debug.Trait PlainTip.t.
      Admitted.
    End Impl_Debug_for_PlainTip.

    (* *******TYPE DEFS******** *)
    (* pub type PolkadotExtrinsicParams<T> = BaseExtrinsicParams<T, PlainTip>; *)
    Definition PolkadotExtrinsicParams (T : Set) `{Config.Trait T} : Set
      := extrinsic_params.BaseExtrinsicParams T PlainTip.
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
      `{config.Config.Trait T}
    : Set := {
      account_id : ref Self -> T::type["AccountId"];
      address : ref Self -> T::type["Address"];
      sign : ref Self -> ref (Slice u8) -> T::type["Signature"];
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
      | Id : AccountId -> t AccountId AccountIndex
      | Index : AccountIndex -> t AccountId AccountIndex
      | Raw :
        alloc.vec.Vec u8 alloc.vec.Vec.Default.A -> t AccountId AccountIndex
      | Address32 : Slice u8 -> t AccountId AccountIndex
      | Address20 : Slice u8 -> t AccountId AccountIndex
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
    Definition ExtrinsicEvents (T : Set) `{subxt.config.Config.Trait T} : Set :=
      ExtrinsicEvents.t T.
  End block_types.
End blocks.
