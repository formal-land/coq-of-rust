Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.proofs.M.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.proofs.lib.
Require CoqOfRust.core.default.
Require CoqOfRust.core.proofs.option.
Require CoqOfRust.examples.default.examples.ink_contracts.proofs.lib.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.erc721.
Require CoqOfRust.examples.default.examples.ink_contracts.erc721.

Import simulations.M.Notations.
Import Run.

(** ** Definition of state and allocation. *)

Module State.
  Record t : Set := {
    storage : option Value.t;
    events : Value.t;
  }.

  Definition of_simulation (x : simulations.erc721.State.t) : t :=
    let '(storage, events) := x in
    {|
      storage := Some (φ storage);
      events := Value.Array (List.map φ events);
    |}.

  Definition of_storage (storage : erc721.Erc721.t) : t := {|
    storage := Some (φ storage);
    events := Value.Array [];
  |}.
End State.

Module Address.
  Inductive t : Set :=
  | storage : t
  | events : t.
End Address.

Module StateInstance.
  Global Instance I : State.Trait State.t Address.t := {
    State.read address state :=
      match address with
      | Address.storage => state.(State.storage)
      | Address.events => Some state.(State.events)
      end;
    State.alloc_write address state value :=
      match address, value with
      | Address.storage, storage =>
        Some (state <| State.storage := Some storage |>)
      | Address.events, events =>
        Some (state <| State.events := events |>)
      end;
  }.

  Lemma is_valid : State.Valid.t I.
    sauto.
  Qed.
End StateInstance.

Module Environment.
  Definition of_env (env : erc721.Env.t) : Value.t :=
    Value.Tuple [
      φ env;
      Value.Pointer (Pointer.Mutable Address.events [])
    ].
End Environment.

Module Balance.
  Module Valid.
    Definition t (x : erc721.Balance.t) : Prop :=
      let 'erc721.Balance.Make x := x in
      Integer.Valid.t Integer.U128 x.
  End Valid.

  Lemma run_Default : default.Default.TraitHasRun erc721.Balance.t.
  Proof.
    constructor.
    eexists; split.
    { unfold IsTraitMethod.
      eexists; split.
      { cbn.
        rewrite erc721.Balance.
        apply core.default.default.Impl_core_default_Default_for_u128.Implements.
      }
      { reflexivity. }
    }
    { unfold Run.pure; intros.
      run_symbolic.
    }
  Qed.
End Balance.

(** ** Verification of the simulations. *)

Module Env.
  (** The simulation [caller] is equal. *)
  Lemma run_caller (env : erc721.Env.t) (state : State.t) :
    let ref_env :=
      Value.Pointer (Pointer.Immediate (φ env)) in
    {{ Environment.of_env env, state |
      erc721.Impl_erc721_Env.caller [] [ref_env] ⇓
      inl (φ (simulations.erc721.Env.caller env))
    | state }}.
  Proof.
    run_symbolic.
  Qed.
  Opaque erc721.Impl_erc721_Env.caller.

  (** The simulation [emit_event] is equal. *)
  Lemma run_emit_event
    (env : erc721.Env.t)
    (event : erc721.Event.t)
    (state : simulations.erc721.State.t) :
    let ref_env :=
      Value.Pointer (Pointer.Immediate (φ env)) in
    let '(storage, events) := state in
    {{ Environment.of_env env, State.of_simulation state |
      erc721.Impl_erc721_Env.emit_event [] [ref_env; φ event] ⇓
      inl (Value.Tuple [])
    | State.of_simulation (
        storage,
        simulations.erc721.Env.emit_event events event
      )
    }}.
  (* This function is axiomatized in the source. *)
  Admitted.
End Env.

(** The simulation [init_env] is equal. *)
Lemma run_init_env (env : erc721.Env.t) (storage : erc721.Erc721.t) :
  let state := State.of_storage storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.init_env [] [] ⇓
    inl (φ (simulations.erc721.init_env env))
  | state }}.
Proof.
(* This function is axiomatized in the source. *)
Admitted.

(** The simulation [env] is equal. *)
Lemma run_env (env : erc721.Env.t) (storage : erc721.Erc721.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.env [] [self] ⇓
    inl (φ (simulations.erc721.env env))
  | state }}.
Proof.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc721.Impl_erc721_Erc721.AssociatedFunction_init_env.
  }
  eapply Run.CallClosure. {
    apply run_init_env.
  }
  run_symbolic.
Qed.
Opaque erc721.Impl_erc721_Erc721.env.

(** The simulation [balance_of_or_zero] is equal. *)
Lemma run_balance_of_or_zero
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (owner : erc721.AccountId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let ref_owner := Value.Pointer (Pointer.Immediate (φ owner)) in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.balance_of_or_zero [] [self; ref_owner] ⇓
    inl (φ (simulations.erc721.balance_of_or_zero storage owner))
  | state }}.
Proof.
  admit.
Admitted.
Opaque erc721.Impl_erc721_Erc721.balance_of_or_zero.

(** The simulation [approved_for_all] is equal. *)
Lemma run_approved_for_all
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (owner : erc721.AccountId.t)
    (operator : erc721.AccountId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.approved_for_all [] [self; φ owner; φ operator] ⇓
    inl (φ (simulations.erc721.approved_for_all storage owner operator))
  | state }}.
Proof.
    admit.
Admitted.

(** The simulation [owner_of] is equal. *)
Lemma run_owner_of
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.owner_of [] [self; φ token_id] ⇓
    inl (φ (simulations.erc721.owner_of storage token_id))
  | state }}.
Proof.
  admit.
Admitted.

(** The simulation [exists] is equal. *)
Lemma run_exists
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.exists_ [] [self; φ token_id] ⇓
    inl (φ (simulations.erc721.exists_ storage token_id))
  | state }}.
Proof.
  admit.
Admitted.

(** The simulation [balance_of] is equal. *)
Lemma run_balance_of
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (owner : erc721.AccountId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.balance_of [] [self; φ owner] ⇓
    inl (φ (simulations.erc721.balance_of storage owner))
  | state }}.
Proof.
  admit.
Admitted.

(** The simulation [get_approved] is equal. *)
Lemma run_get_approved
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.get_approved [] [self; φ token_id] ⇓
    inl (φ (simulations.erc721.get_approved storage token_id))
  | state }}.
Proof.
  admit.
Admitted.

(** The simulation [is_approved_for_all] is equal. *)
Lemma run_is_approved_for_all
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (owner : erc721.AccountId.t)
    (operator : erc721.AccountId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.is_approved_for_all [] [self; φ owner; φ operator] ⇓
    inl (φ (simulations.erc721.is_approved_for_all storage owner operator))
  | state }}.
Proof.
  admit.
Admitted.

Module Output.
  Record t : Set := {
    result : Value.t + Exception.t;
    state : State.t;
  }.
  Arguments t : clear implicits.
End Output.

Definition lift_simulation {A : Set} `{ToValue A}
  (simulation : MS? simulations.erc721.State.t string A)
  (storage : erc721.Erc721.t) :
  Output.t :=
  let '(result, (storage, events)) := simulation (storage, []) in
  let result :=
    match result with
    | inl result => inl (φ result)
    | inr error => inr (M.Exception.Panic error)
    end in
  {|
    Output.result := result;
    Output.state := State.of_simulation (storage, events);
  |}.

(** The simulation [clear_approval] is equal. *)
Lemma run_clear_approval
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let simulation :=
    lift_simulation
      (simulations.erc721.clear_approval token_id) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.clear_approval [] [self; φ token_id] ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.

(** The simulation [set_approval_for_all] is equal. *)
Lemma run_set_approval_for_all
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (to : erc721.AccountId.t)
    (approved : bool) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let simulation :=
    lift_simulation
      (simulations.erc721.set_approval_for_all env to approved) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.set_approval_for_all [] [self; φ to; φ approved] ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.

(** The simulation [approve_for] is equal. *)
Lemma run_approve_for
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (to : erc721.AccountId.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let simulation :=
    lift_simulation
      (simulations.erc721.approve_for env to token_id) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.approve_for [] [self; φ to; φ token_id] ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.


(** The simulation [approve] is equal. *)
Lemma run_approve
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (to : erc721.AccountId.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let simulation :=
    lift_simulation
      (simulations.erc721.approve env to token_id) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.approve [] [self; φ to; φ token_id] ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.

(** The simulation [remove_token_from] is equal. *)
Lemma run_remove_token_from
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (from : erc721.AccountId.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let simulation :=
    lift_simulation
      (simulations.erc721.remove_token_from from token_id) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.remove_token_from [] [self; φ from; φ token_id] ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.

(** The simulation [add_token_to] is equal. *)
Lemma run_add_token_to
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (to : erc721.AccountId.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let simulation :=
    lift_simulation
      (simulations.erc721.add_token_to to token_id) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.add_token_to [] [self; φ to; φ token_id] ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.

(** The simulation [transfer_token_from] is equal. *)
Lemma run_transfer_token_from
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (from : erc721.AccountId.t)
    (to : erc721.AccountId.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let simulation :=
    lift_simulation
      (simulations.erc721.transfer_token_from env from to token_id) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.transfer_token_from [] [self; φ from; φ to; φ token_id] ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.

(** The simulation [transfer] is equal. *)
Lemma run_transfer
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (to : erc721.AccountId.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let simulation :=
    lift_simulation
      (simulations.erc721.transfer env to token_id) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.transfer [] [self; φ to; φ token_id] ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.

(** The simulation [tansfer_from] is equal. *)
Lemma run_transfer_from
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (from : erc721.AccountId.t)
    (to : erc721.AccountId.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let simulation :=
    lift_simulation
      (simulations.erc721.transfer_from env from to token_id) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.transfer_from [] [self; φ from; φ to; φ token_id] ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.

(** The simulation [mint] is equal. *)
Lemma run_mint
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (to : erc721.AccountId.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let simulation :=
    lift_simulation
      (simulations.erc721.mint env token_id) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.mint [] [self; φ token_id] ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.

(** The simulation [burn] is equal. *)
Lemma run_burn
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (token_id : erc721.TokenId.t) :
  let state := State.of_storage storage in
  let self := Value.Pointer (Pointer.Mutable Address.storage []) in
  let simulation :=
    lift_simulation
      (simulations.erc721.burn env token_id) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721.burn [] [self; φ token_id] ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.
