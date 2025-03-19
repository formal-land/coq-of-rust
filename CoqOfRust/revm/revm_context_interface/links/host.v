Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

(*
pub trait Host: TransactionGetter + BlockGetter + CfgGetter {
    fn load_account_delegated(&mut self, address: Address) -> Option<AccountLoad>;
    fn block_hash(&mut self, number: u64) -> Option<B256>;
    fn balance(&mut self, address: Address) -> Option<StateLoad<U256>>;
    fn code(&mut self, address: Address) -> Option<Eip7702CodeLoad<Bytes>>;
    fn code_hash(&mut self, address: Address) -> Option<Eip7702CodeLoad<B256>>;
    fn sload(&mut self, address: Address, index: U256) -> Option<StateLoad<U256>>;
    fn sstore(
        &mut self,
        address: Address,
        index: U256,
        value: U256,
    ) -> Option<StateLoad<SStoreResult>>;
    fn tload(&mut self, address: Address, index: U256) -> U256;
    fn tstore(&mut self, address: Address, index: U256, value: U256);
    fn log(&mut self, log: Log);
    fn selfdestruct(
        &mut self,
        address: Address,
        target: Address,
    ) -> Option<StateLoad<SelfDestructResult>>;
}
*)
Module Host.
  (* TODO *)
  Class Run (Self : Set) `{Link Self} : Set := {
    TODO : unit;
  }.
End Host.
