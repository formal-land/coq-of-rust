Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.

(*
pub trait Host: TransactionGetter + BlockGetter + CfgGetter {
    /// Load an account code.
    fn load_account_delegated(&mut self, address: Address) -> Option<AccountLoad>;

    /// Gets the block hash of the given block `number`.
    fn block_hash(&mut self, number: u64) -> Option<B256>;

    /// Gets balance of `address` and if the account is cold.
    fn balance(&mut self, address: Address) -> Option<StateLoad<U256>>;

    /// Gets code of `address` and if the account is cold.
    fn code(&mut self, address: Address) -> Option<Eip7702CodeLoad<Bytes>>;

    /// Gets code hash of `address` and if the account is cold.
    fn code_hash(&mut self, address: Address) -> Option<Eip7702CodeLoad<B256>>;

    /// Gets storage value of `address` at `index` and if the account is cold.
    fn sload(&mut self, address: Address, index: U256) -> Option<StateLoad<U256>>;

    /// Sets storage value of account address at index.
    ///
    /// Returns [`StateLoad`] with [`SStoreResult`] that contains original/new/old storage value.
    fn sstore(
        &mut self,
        address: Address,
        index: U256,
        value: U256,
    ) -> Option<StateLoad<SStoreResult>>;

    /// Gets the transient storage value of `address` at `index`.
    fn tload(&mut self, address: Address, index: U256) -> U256;

    /// Sets the transient storage value of `address` at `index`.
    fn tstore(&mut self, address: Address, index: U256, value: U256);

    /// Emits a log owned by `address` with given `LogData`.
    fn log(&mut self, log: Log);

    /// Marks `address` to be deleted, with funds transferred to `target`.
    fn selfdestruct(
        &mut self,
        address: Address,
        target: Address,
    ) -> Option<StateLoad<SelfDestructResult>>;
}
*)
Module Host.
  Class Trait (Self : Set) := {
    (* TODO *)
  }.
End Host.
