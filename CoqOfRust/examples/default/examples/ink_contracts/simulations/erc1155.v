Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.core.simulations.default.
Require Import CoqOfRust.core.simulations.option.
Require Import CoqOfRust.core.simulations.bool.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.lib.
Require Import CoqOfRust.simulations.M.

(* TODO:
- Check the Mapping structure in erc1155

*)

(* ******** Primitives ******** *)

(* 
struct AccountId(u128);
*)
Module AccountId.
  Inductive t : Set :=
  | Make (account_id : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc1155::AccountId";
    φ '(Make account_id) :=
      Value.StructTuple "erc1155::AccountId" [Value.Integer Integer.U128 account_id];
  }.
End AccountId.

(* type Balance = u128; *)
Module Balance.
  Inductive t : Set :=
  | Make (balance : Z).

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "erc1155::Balance";
  }.

  Global Instance IsToValue : ToValue t := {
    φ '(Make balance) :=
      Value.StructTuple "erc1155::Balance" [Value.Integer Integer.U128 balance];
  }.
End Balance.

(* 
struct Env {
    caller: AccountId,
}
*)

Module Env.
  Record t : Set := {
    caller : AccountId.t;
  }.

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "erc1155::Env";
  }.

  Global Instance IsToValue : ToValue t := {
    φ '(Make x) :=
      Value.StructTuple "erc1155::Env" φ x;
  }.
End Env.

(* ******** IN PROGRESS ******** *)

(* 
fn zero_address() -> AccountId {
    [0u8; 32].into()
}
*)

(* 
const ON_ERC_1155_RECEIVED_SELECTOR: [u8; 4] = [0xF2, 0x3A, 0x6E, 0x61];
*)

(* 
const _ON_ERC_1155_BATCH_RECEIVED_SELECTOR: [u8; 4] = [0xBC, 0x19, 0x7C, 0x81];
*)

(* pub type TokenId = u128; *)
Module TokenId.
  Inductive t : Set :=
  | Make (token_id : Z).

  Global Instance IsToTy : ToTy t := {
    Φ := Ty.path "erc1155::TokenId";
  }.

  Global Instance IsToValue : ToValue t := {
    φ '(Make token_id) :=
      Value.StructTuple "erc1155::TokenId" [Value.Integer Integer.U128 token_id];
  }.
End TokenId. 

(* 
// The ERC-1155 error types.
#[derive(PartialEq, Eq)]
pub enum Error {
    /// This token ID has not yet been created by the contract.
    UnexistentToken,
    /// The caller tried to sending tokens to the zero-address (`0x00`).
    ZeroAddressTransfer,
    /// The caller is not approved to transfer tokens on behalf of the account.
    NotApproved,
    /// The account does not have enough funds to complete the transfer.
    InsufficientBalance,
    /// An account does not need to approve themselves to transfer tokens.
    SelfApproval,
    /// The number of tokens being transferred does not match the specified number of
    /// transfers.
    BatchTransferMismatch,
}
*)
Module Error.
  Inductive t : Set :=
  | UnexistentToken
  | ZeroAddressTransfer
  | NotApproved
  | InsufficientBalance
  | SelfApproval
  | BatchTransferMismatch.

  (* TODO: finish the ToValue here? *)
End Error.

(* pub type Result<T> = core::result::Result<T, Error>; *)
Module Result.
  (* TODO: Check if this is the right way to use the Result *)
  Definition t (T : Set) : Set := core.result.Result T Error.
End Result.

(* pub trait Erc1155 { .. }*)
Module Erc1155.
  Class Trait (Self : Set) : Set := {
  (* 
    fn safe_transfer_from(
        &mut self,
        from: AccountId,
        to: AccountId,
        token_id: TokenId,
        value: Balance,
        data: Vec<u8>,
    ) -> Result<()>;
  *)

  (* fn safe_batch_transfer_from(
      &mut self,
      from: AccountId,
      to: AccountId,
      token_ids: Vec<TokenId>,
      values: Vec<Balance>,
      data: Vec<u8>,
  ) -> Result<()>; *)

  (* fn balance_of(&self, owner: AccountId, token_id: TokenId) -> Balance; *)

  (* fn balance_of_batch(&self, owners: Vec<AccountId>, token_ids: Vec<TokenId>) -> Vec<Balance>; *)

  (* fn set_approval_for_all(&mut self, operator: AccountId, approved: bool) -> Result<()>; *)
  
  (* fn is_approved_for_all(&self, owner: AccountId, operator: AccountId) -> bool; *)

  }.
End Erc1155.

(* pub trait Erc1155TokenReceiver { .. } *)
Module Erc1155TokenReceiver.
  Class Trait (Self : Set) : Set := { 
  (* fn on_received(
      &mut self,
      operator: AccountId,
      from: AccountId,
      token_id: TokenId,
      value: Balance,
      data: Vec<u8>,
  ) -> Vec<u8>; *)

  (* fn on_batch_received(
      &mut self,
      operator: AccountId,
      from: AccountId,
      token_ids: Vec<TokenId>,
      values: Vec<Balance>,
      data: Vec<u8>,
  ) -> Vec<u8>; *)
  }.
End Erc1155TokenReceiver.

(* type Owner = AccountId;
type Operator = AccountId; *)

(* pub struct TransferSingle {
    operator: Option<AccountId>,
    from: Option<AccountId>,
    to: Option<AccountId>,
    token_id: TokenId,
    value: Balance,
} *)
Module TransferSingle.
  Record t : Set := {

  }.
End TransferSingle.

(* pub struct ApprovalForAll {
    owner: AccountId,
    operator: AccountId,
    approved: bool,
}

pub struct Uri {
    value: String,
    token_id: TokenId,
}

enum Event {
    TransferSingle(TransferSingle),
    ApprovalForAll(ApprovalForAll),
    Uri(Uri),
} *)
