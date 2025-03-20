Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.revm.links.dependencies.
Require Import CoqOfRust.revm.revm_context_interface.links.cfg.
Require Import CoqOfRust.revm.revm_context_interface.links.block.
Require Import CoqOfRust.revm.revm_context_interface.links.journaled_state.

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
  Module Types.
    Record t : Type := {
      Cfg : Set; (* For CfgGetter *)
      Spec : Set; (* For CfgGetter *)
      Block : Set; (* For BlockGetter *)
    }.

    Class AreLinks (types : t) : Set := {
      H_Cfg : Link types.(Cfg);
      H_Spec : Link types.(Spec);
      H_Block : Link types.(Block);
    }.

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

  Definition Run_load_account_delegated (Self : Set) `{Link Self} : Set :=
    {load_account_delegated @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "load_account_delegated" load_account_delegated *
      forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (address : alloy_primitives.bits.links.address.Address.t),
        {{ load_account_delegated [] [] [ φ self; φ address ] 🔽 option AccountLoad.t }}
    }.

  Definition Run_block_hash (Self : Set) `{Link Self} : Set :=
    {block_hash @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "block_hash" block_hash *
      forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (number : U64.t),
        {{ block_hash [] [] [ φ self; φ number ] 🔽 option B256.t }}
    }.

  Definition Run_balance (Self : Set) `{Link Self} : Set :=
    {balance @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "balance" balance *
      forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (address : alloy_primitives.bits.links.address.Address.t),
        {{ balance [] [] [ φ self; φ address ] 🔽 option (StateLoad.t U256.t) }}
    }.

  Definition Run_code (Self : Set) `{Link Self} : Set :=
    {code @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "code" code *
      forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (address : alloy_primitives.bits.links.address.Address.t),
        {{ code [] [] [ φ self; φ address ] 🔽 option (Eip7702CodeLoad.t alloy_primitives.links.bytes_.Bytes.t) }}
    }.

  Definition Run_code_hash (Self : Set) `{Link Self} : Set :=
    {code_hash @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "code_hash" code_hash *
      forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (address : alloy_primitives.bits.links.address.Address.t),
        {{ code_hash [] [] [ φ self; φ address ] 🔽 option (Eip7702CodeLoad.t B256.t) }}
    }.

  Definition Run_sload (Self : Set) `{Link Self} : Set :=
    {sload @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "sload" sload *
      forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (address : alloy_primitives.bits.links.address.Address.t)
          (index : U256.t),
        {{ sload [] [] [ φ self; φ address; φ index ] 🔽 option (StateLoad.t U256.t) }}
    }.

  Definition Run_sstore (Self : Set) `{Link Self} : Set :=
    {sstore @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "sstore" sstore *
      forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (address : alloy_primitives.bits.links.address.Address.t)
          (index : U256.t)
          (value : U256.t),
        {{ sstore [] [] [ φ self; φ address; φ index; φ value ] 🔽 option (StateLoad.t SStoreResult.t) }}
    }.

  Definition Run_tload (Self : Set) `{Link Self} : Set :=
    {tload @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "tload" tload *
      forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (address : alloy_primitives.bits.links.address.Address.t)
          (index : U256.t),
        {{ tload [] [] [ φ self; φ address; φ index ] 🔽 U256.t }}
    }.

  Definition Run_tstore (Self : Set) `{Link Self} : Set :=
    {tstore @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "tstore" tstore *
      forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (address : alloy_primitives.bits.links.address.Address.t)
          (index : U256.t)
          (value : U256.t),
        {{ tstore [] [] [ φ self; φ address; φ index; φ value ] 🔽 unit }}
    }.

  Definition Run_log (Self : Set) `{Link Self} : Set :=
    {log @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "log" log *
      forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (log' : Log.t),
        {{ log [] [] [ φ self; φ log' ] 🔽 unit }}
    }.

  Definition Run_selfdestruct (Self : Set) `{Link Self} : Set :=
    {selfdestruct @
      IsTraitMethod.t "revm_context_interface::cfg::Cfg" [] [] (Φ Self) "selfdestruct" selfdestruct *
      forall
          (self : Ref.t Pointer.Kind.MutRef Self)
          (address : alloy_primitives.bits.links.address.Address.t)
          (target : alloy_primitives.bits.links.address.Address.t),
        {{ selfdestruct [] [] [ φ self; φ address; φ target ] 🔽 option (StateLoad.t SelfDestructResult.t) }}
    }.

  Record Run (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
  {
    run_BlockGetter : BlockGetter.Run Self (Types.to_BlockGetter_types types);
    run_CfgGetter : CfgGetter.Run Self (Types.to_CfgGetter_types types);
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
End Host.
