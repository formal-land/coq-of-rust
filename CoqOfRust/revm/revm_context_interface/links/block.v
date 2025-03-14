Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
(* Require Import CoqOfRust.core.convert.links.mod. *)
Require Import CoqOfRust.revm.links.dependencies.
(* Require Import CoqOfRust.revm.revm_specification.links.hardfork. *)
(* TODO: import for Address *)

(* 
#[auto_impl(&, &mut, Box, Arc)]
pub trait Block {
    fn number(&self) -> u64;

    fn beneficiary(&self) -> Address;

    fn timestamp(&self) -> u64;

    fn gas_limit(&self) -> u64;

    fn basefee(&self) -> u64;

    fn difficulty(&self) -> U256;

    fn prevrandao(&self) -> Option<B256>;

    fn blob_excess_gas_and_price(&self) -> Option<BlobExcessGasAndPrice>;

    fn blob_gasprice(&self) -> Option<u128> {
        self.blob_excess_gas_and_price().map(|a| a.blob_gasprice)
    }

    fn blob_excess_gas(&self) -> Option<u64> {
        self.blob_excess_gas_and_price().map(|a| a.excess_blob_gas)
    }
}
*)
Module Block. 
  (* 
    fn beneficiary(&self) -> Address;
  *)
End Block. 