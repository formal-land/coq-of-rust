Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
(* Require Import CoqOfRust.core.convert.links.mod. *)
Require Import CoqOfRust.revm.links.dependencies.
(* Require Import CoqOfRust.revm.revm_specification.links.hardfork. *)

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

  (* fn number(&self) -> u64; *)
  Definition Run_number (Self : Set) `{Link Self} : Set :=
    {number @
      IsTraitMethod.t "revm_context_interface::block::Block" [] [] (Φ Self) "number" number *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ number [] [] [ φ self ] 🔽 U64.t }}
    }.

  Definition Run_beneficiary (Self : Set) `{Link Self} : Set :=
    {beneficiary @
      IsTraitMethod.t "revm_context_interface::block::Block" [] [] (Φ Self) "beneficiary" beneficiary *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ beneficiary [] [] [ φ self ] 🔽 Address.t }}
    }.

  (* fn timestamp(&self) -> u64; *)
  Definition Run_timestamp (Self : Set) `{Link Self} : Set :=
    {timestamp @
      IsTraitMethod.t "revm_context_interface::block::Block" [] [] (Φ Self) "timestamp" timestamp *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ timestamp [] [] [ φ self ] 🔽 U64.t }}
    }.

  (* fn gas_limit(&self) -> u64; *)
  Definition Run_gas_limit (Self : Set) `{Link Self} : Set :=
    {gas_limit @
      IsTraitMethod.t "revm_context_interface::block::Block" [] [] (Φ Self) "gas_limit" gas_limit *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ gas_limit [] [] [ φ self ] 🔽 U64.t }}
    }.

  (* fn basefee(&self) -> u64; *)

  (* fn difficulty(&self) -> U256; *)

  (* fn blob_gasprice(&self) -> Option<u128> *)

  Record Run (Self : Set) `{Link Self} : Set := {
    beneficiary : Run_beneficiary Self;
    timestamp : Run_timestamp Self;
    gas_limit : Run_gas_limit Self;
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

  Definition Run_block (Self : Set) `{Link Self} : Set :=
    {block @
      IsTraitMethod.t "revm_context_interface::block::BlockGetter" [] [] (Φ Self) "block" block *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ block [] [] [ φ self ] 🔽 unit }}
    }.

  Record Run (Self : Set) `{Link Self} (types : Types.t)  `{Types.AreLinks types} : Set := {
    Block_IsAssociated : 
      IsTraitAssociatedType
        "revm_context_interface::block::BlockGetter" [] [] (Φ Self)
        "Block" (Φ types.(Types.Block));
    run_Block_for_Block : Block.Run types.(Types.Block);
    block : Run_block Self;
  }.
End BlockGetter.