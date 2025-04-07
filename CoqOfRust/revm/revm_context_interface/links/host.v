Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.bytes.links.mod.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.log.links.mod.
Require Import revm.revm_context_interface.links.cfg.
Require Import revm.revm_context_interface.links.block.
Require Import revm.revm_context_interface.links.journaled_state.
Require Import revm.revm_context_interface.links.transaction.

(*
pub struct SStoreResult {
    pub original_value: U256,
    pub present_value: U256,
    pub new_value: U256,
}
*)
Module SStoreResult.
  Parameter t : Set.

  Global Instance IsLink : Link t.
  Admitted.
End SStoreResult.

(*
pub struct SelfDestructResult {
    pub had_value: bool,
    pub target_exists: bool,
    pub previously_destroyed: bool,
}
*)
Module SelfDestructResult.
  Parameter t : Set.

  Global Instance IsLink : Link t.
  Admitted.
End SelfDestructResult.

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
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::host::Host", [], [], Φ Self).

  Module Types.
    Record t : Type := {
      Transaction : Set;
      TransactionTypes : Transaction.Types.t;
      Cfg : Set; (* For CfgGetter *)
      Spec : Set; (* For CfgGetter *)
      Block : Set; (* For BlockGetter *)
    }.

    Class AreLinks (types : t) : Set := {
      H_Transaction : Link types.(Transaction);
      H_TransactionTypes : Transaction.Types.AreLinks types.(TransactionTypes);
      H_Cfg : Link types.(Cfg);
      H_Spec : Link types.(Spec);
      H_Block : Link types.(Block);
    }.

    Global Instance IsLinkTransaction (types : t) (H : AreLinks types) : Link types.(Transaction) :=
      H.(H_Transaction _).
    Global Instance AreLinksTransactionTypes (types : t) (H : AreLinks types) :
      Transaction.Types.AreLinks types.(TransactionTypes) :=
      H.(H_TransactionTypes _).
    Global Instance IsLinkCfg (types : t) (H : AreLinks types) : Link types.(Cfg) :=
      H.(H_Cfg _).
    Global Instance IsLinkSpec (types : t) (H : AreLinks types) : Link types.(Spec) :=
      H.(H_Spec _).
    Global Instance IsLinkBlock (types : t) (H : AreLinks types) : Link types.(Block) :=
      H.(H_Block _).

    Definition to_BlockGetter_types (types : t) : BlockGetter.Types.t :=
      {|
        BlockGetter.Types.Block := types.(Block);
      |}.

    Global Instance AreLinks_to_BlockGetter_types (types : t) (H : AreLinks types) :
      BlockGetter.Types.AreLinks (to_BlockGetter_types types) :=
      {|
        BlockGetter.Types.H_Block := _;
      |}.

    Definition to_CfgGetter_types (types : t) : CfgGetter.Types.t :=
      {|
        CfgGetter.Types.Cfg := types.(Cfg);
        CfgGetter.Types.Spec := types.(Spec);
      |}.

    Global Instance AreLinks_to_CfgGetter_types (types : t) (H : AreLinks types) :
      CfgGetter.Types.AreLinks (to_CfgGetter_types types) :=
      {|
        CfgGetter.Types.H_Cfg := _;
        CfgGetter.Types.H_Spec := _;
      |}.
  End Types.

  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::host::Host", [], [], Φ Self).

  (* fn load_account_delegated(&mut self, address: Address) -> Option<AccountLoad>; *)
  Definition Run_load_account_delegated (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "load_account_delegated" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (address : Address.t),
        Run.Trait method [] [] [ φ self; φ address ] (option AccountLoad.t)
    ).

  (* fn block_hash(&mut self, number: u64) -> Option<B256>; *)
  Definition Run_block_hash (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "block_hash" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (number : U64.t),
        Run.Trait method [] [] [ φ self; φ number ] (option aliases.B256.t)
    ).

  (* fn balance(&mut self, address: Address) -> Option<StateLoad<U256>>; *)
  Definition Run_balance (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "balance" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (address : Address.t),
        Run.Trait method [] [] [ φ self; φ address ] (option (StateLoad.t aliases.U256.t))
    ).

  (* fn code(&mut self, address: Address) -> Option<Eip7702CodeLoad<Bytes>>; *)
  Definition Run_code (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "code" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (address : Address.t),
        Run.Trait method [] [] [ φ self; φ address ] (option (Eip7702CodeLoad.t Bytes.t))
    ).

  (* fn code_hash(&mut self, address: Address) -> Option<Eip7702CodeLoad<B256>>; *)
  Definition Run_code_hash (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "code_hash" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (address : Address.t),
        Run.Trait method [] [] [ φ self; φ address ] (option (Eip7702CodeLoad.t aliases.B256.t))
    ).

  (* fn sload(&mut self, address: Address, index: U256) -> Option<StateLoad<U256>>; *)
  Definition Run_sload (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "sload" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self)
             (address : Address.t)
             (index : aliases.U256.t),
        Run.Trait method [] [] [ φ self; φ address; φ index ] (option (StateLoad.t aliases.U256.t))
    ).

  (* 
  fn sstore(
      &mut self,
      address: Address,
      index: U256,
      value: U256,
  ) -> Option<StateLoad<SStoreResult>>;
  *)
  Definition Run_sstore (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "sstore" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self)
             (address : Address.t)
             (index : aliases.U256.t)
             (value : aliases.U256.t),
        Run.Trait method [] [] [ φ self; φ address; φ index; φ value ] (option (StateLoad.t SStoreResult.t))
    ).

  (* fn tload(&mut self, address: Address, index: U256) -> U256; *)
  Definition Run_tload (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "tload" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self)
             (address : Address.t)
             (index : aliases.U256.t),
        Run.Trait method [] [] [ φ self; φ address; φ index ] aliases.U256.t
    ).

  (* fn tstore(&mut self, address: Address, index: U256, value: U256); *)
  Definition Run_tstore (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "tstore" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self)
             (address : Address.t)
             (index : aliases.U256.t)
             (value : aliases.U256.t),
        Run.Trait method [] [] [ φ self; φ address; φ index; φ value ] unit
    ).

  (* fn log(&mut self, log: Log); *)
  Definition Run_log (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "log" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self)
             (log' : Log.t),
        Run.Trait method [] [] [ φ self; φ log' ] unit
    ).

  (* 
  fn selfdestruct(
    &mut self,
    address: Address,
    target: Address,
  ) -> Option<StateLoad<SelfDestructResult>>;
  *)
  Definition Run_selfdestruct (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "selfdestruct" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self)
             (address : Address.t)
             (target : Address.t),
        Run.Trait method [] [] [ φ self; φ address; φ target ] (option (StateLoad.t SelfDestructResult.t))
    ).

  Class Run (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set := {
    run_TransactionGetter_for_Self :
      TransactionGetter.Run Self types.(Types.Transaction) types.(Types.TransactionTypes);
    run_BlockGetter_for_Self : BlockGetter.Run Self (Types.to_BlockGetter_types types);
    run_CfgGetter_for_Self : CfgGetter.Run Self (Types.to_CfgGetter_types types);
    load_account_delegated : Run_load_account_delegated Self;
    block_hash : Run_block_hash Self;
    balance : Run_balance Self;
    code : Run_code Self;
    code_hash : Run_code_hash Self;
    sload : Run_sload Self;
    sstore : Run_sstore Self;
    tload : Run_tload Self;
    tstore : Run_tstore Self;
    log : Run_log Self;
    selfdestruct : Run_selfdestruct Self;
  }.

  Ltac destruct_run :=
    cbn;
    eapply Run.Rewrite; [
      progress repeat erewrite IsTraitAssociatedType_eq
        by match goal with
        | H : Run _ _ |- _ => apply H
        end;
      reflexivity
    |];
    match goal with
    | H : Run _ _ |- _ =>
      (* We make a duplicate for future calls *)
      pose H;
      destruct H
    end.
End Host.
