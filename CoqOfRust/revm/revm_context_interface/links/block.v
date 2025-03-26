Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.revm.links.dependencies.

Module Address := dependencies.alloy_primitives.bits.links.address.Address.

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
  Parameter t : Set.

  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::block::Block", [], [], Φ Self).

  (* fn number(&self) -> u64; *)
  Definition Run_number (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "number" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U64.t
    ).

  (* fn beneficiary(&self) -> Address; *)
  Definition Run_beneficiary (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "beneficiary" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] Address.t
    ).

  (* fn timestamp(&self) -> u64; *)
  Definition Run_timestamp (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "timestamp" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U64.t
    ).

  (* fn gas_limit(&self) -> u64; *)
  Definition Run_gas_limit (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "gas_limit" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U64.t
    ).

  (* fn basefee(&self) -> u64; *)
  Definition Run_basefee (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "basefee" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U64.t
    ).

  (* fn difficulty(&self) -> U256; *)
  Definition Run_difficulty (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "difficulty" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U256.t
    ).

  (* fn blob_gasprice(&self) -> Option<u128> *)
  Definition Run_blob_gasprice (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "blob_gasprice" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] (option U128.t)
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    number : Run_number Self;
    beneficiary : Run_beneficiary Self;
    timestamp : Run_timestamp Self;
    gas_limit : Run_gas_limit Self;
    basefee : Run_basefee Self;
    difficulty : Run_difficulty Self;
    blob_gasprice : Run_blob_gasprice Self;
  }.
End Block. 

(* 
#[auto_impl(&, &mut, Box, Arc)]
pub trait BlockGetter {
    type Block: Block;

    fn block(&self) -> &Self::Block;
}
*)
Module BlockGetter.
  Module Types.
    Record t : Type := {
      Block : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_Block : Link types.(Block);
    }.

    Global Instance IsLinkBlock (types : t) (H : AreLinks types) : Link types.(Block) :=
      H.(H_Block _).
  End Types.

  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::block::BlockGetter", [], [], Φ Self).

  Definition Run_block (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "block" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] unit
    ).

  (* (* NOTE: Question: since `BlockGetter` "inherhits" several methods from `Block` trait, 
    do we still need to additionally write instances for these methods? *)
  (* fn timestamp(&self) -> u64; *)
  Definition Run_timestamp (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "timestamp" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
        Run.Trait method [] [] [ φ self ] U64.t
    ). *)

  Class Run (Self : Set) `{Link Self} (types : Types.t)  `{Types.AreLinks types} : Set := {
    Block_IsAssociated : 
      IsTraitAssociatedType
        "revm_context_interface::block::BlockGetter" [] [] (Φ Self)
        "Block" (Φ types.(Types.Block));
    run_Block_for_Block : Block.Run types.(Types.Block);
    block : Run_block Self;
    (* timestamp : Run_timestamp Self; *)
  }.
End BlockGetter.