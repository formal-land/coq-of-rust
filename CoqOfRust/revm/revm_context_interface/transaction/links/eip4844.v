Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.links.aliases.

(*
pub trait Eip4844Tx: Eip1559CommonTxFields {
    fn destination(&self) -> Address;
    fn blob_versioned_hashes(&self) -> &[B256];
    fn max_fee_per_blob_gas(&self) -> u128;
    fn total_blob_gas(&self) -> u64;
    fn calc_max_data_fee(&self) -> U256;
}
*)
Module Eip4844Tx.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::transaction::eip4844::Eip4844Tx", [], [], Φ Self).

  Definition Run_destination
    (Self : Set) `{Link Self} :
    Set :=
    TraitMethod.C (trait Self) "destination" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Address.t
    ).

  Definition Run_blob_versioned_hashes
    (Self : Set) `{Link Self} :
    Set :=
    TraitMethod.C (trait Self) "blob_versioned_hashes" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref (list aliases.B256.t))
    ).

  Definition Run_max_fee_per_blob_gas
    (Self : Set) `{Link Self} :
    Set :=
    TraitMethod.C (trait Self) "max_fee_per_blob_gas" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] U128.t
    ).

  Definition Run_total_blob_gas
    (Self : Set) `{Link Self} :
    Set :=
    TraitMethod.C (trait Self) "total_blob_gas" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] U64.t
    ).

  Definition Run_calc_max_data_fee
    (Self : Set) `{Link Self} :
    Set :=
    TraitMethod.C (trait Self) "calc_max_data_fee" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] aliases.U256.t
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    (* TODO *)
    (* run_Eip1559CommonTxFields_for_Self : Eip1559CommonTxFields.Run Self; *)
    destination : Run_destination Self;
    blob_versioned_hashes : Run_blob_versioned_hashes Self;
    max_fee_per_blob_gas : Run_max_fee_per_blob_gas Self;
    total_blob_gas : Run_total_blob_gas Self;
    calc_max_data_fee : Run_calc_max_data_fee Self;
  }.
End Eip4844Tx.
