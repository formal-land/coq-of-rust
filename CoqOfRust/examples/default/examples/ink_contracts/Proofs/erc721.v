Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.Proofs.M.
Require Import CoqOfRust.lib.Proofs.lib.
Require CoqOfRust.examples.default.examples.ink_contracts.Proofs.Lib.
Require CoqOfRust.examples.default.examples.ink_contracts.Simulations.erc721.
Require CoqOfRust.examples.default.examples.ink_contracts.erc721.

Import Simulations.M.Notations.
Import Run.

(** ** Definition of state and allocation. *)

Module State.
  Record t : Set := {
    storage : option erc721.Erc721.t;
    events : list erc721.Event.t;
  }.

  Definition of_storage (storage : erc721.Erc721.t) : t := {|
    storage := Some storage;
    events := [];
  |}.
End State.

Module Address.
  Inductive t : Set :=
  | storage : t
  | events : t
  .
End Address.

Module StateInstance.
  Global Instance I : State.Trait State.t Address.t := {
    State.get_Set address :=
      match address with
      | Address.storage => erc721.Erc721.t
      | Address.events => list erc721.Event.t
      end;
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
  Proof.
    sauto lq: on rew: off.
  Qed.
End StateInstance.

Module Environment.
  Definition t : Set :=
    erc721.Env.t * M.Val (list erc721.Event.t).

  Definition of_env (env : erc721.Env.t) : t :=
    (env, Ref.mut_ref Address.events).
End Environment.

(** ** Verification of the simulations. *)

Module Env.
  (** The simulation [caller] is equal. *)
  Lemma run_caller (env : erc721.Env.t) (state : State.t) :
    let ref_env := Ref.Imm env in
    {{ Environment.of_env env, state |
      erc721.Impl_erc721_Env_t.caller ref_env ⇓
      inl (Simulations.erc721.Env.caller env)
    | state }}.
  Proof.
    run_symbolic.
  Qed.
  Opaque erc721.Impl_erc721_Env_t.caller.

  (** The simulation [emit_event] is equal. *)
  Lemma run_emit_event
    (env : erc721.Env.t)
    (event : erc721.Event.t)
    (state : State.t) :
    let ref_env := Ref.Imm env in
    {{ Environment.of_env env, state |
      erc721.Impl_erc721_Env_t.emit_event ref_env event ⇓
      inl tt
    | state <|
        State.events :=
          Simulations.erc721.Env.emit_event state.(State.events) event
      |>
    }}.
  Proof.
    run_symbolic.
  Qed.
  Opaque erc721.Impl_erc721_Env_t.emit_event.
End Env.

(** The simulation [env] is equal. *)
Lemma run_env (env : erc721.Env.t) (storage : erc721.Erc721.t) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721_t.env self ⇓
    inl (Simulations.erc721.env env)
  | state }}.
Proof.
  run_symbolic.
  eapply Run.Call. {
    run_symbolic.
  }
  run_symbolic.
Qed.
Opaque erc721.Impl_erc721_Erc721_t.env.

(** The simulation [balance_of_or_zero] is equal. *)
Lemma run_balance_of_or_zero
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (owner : erc721.AccountId.t) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  let ref_owner : ref erc721.AccountId.t := Ref.Imm owner in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721_t.balance_of_or_zero self ref_owner ⇓
    inl (Simulations.erc721.balance_of_or_zero storage owner)
  | state }}.
Proof.
  unfold
    erc721.Impl_erc721_Erc721_t.balance_of_or_zero,
    Simulations.erc721.balance_of_or_zero.
  run_symbolic.
  eapply Run.Call. {
    run_symbolic.
  }
  run_symbolic.
  destruct Lib.Mapping.get; eapply Run.Call; run_symbolic.
Qed.
Opaque erc721.Impl_erc721_Erc721_t.balance_of_or_zero.

(** The simulation [approved_for_all] is equal. *)
Lemma run_approved_for_all
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (owner : erc721.AccountId.t)
    (operator : erc721.AccountId.t) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  let ref_owner : ref erc721.AccountId.t := Ref.Imm owner in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721_t.approved_for_all self owner operator ⇓
    inl (Simulations.erc721.approved_for_all storage owner operator)
  | state }}.
Proof.
  admit.
Admitted.

(** The simulation [owner_of] is equal. *)
Lemma run_owner_of
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (token_id : ltac:(erc721.TokenId)) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721_t.owner_of self token_id ⇓
    inl (Simulations.erc721.owner_of storage token_id)
  | state }}.
Proof.
  admit.
Admitted.

(** The simulation [exists] is equal. *)
Lemma run_exists
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (token_id : ltac:(erc721.TokenId)) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721_t.exists_ self token_id ⇓
    inl (Simulations.erc721.exists_ storage token_id)
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
  let self := Ref.mut_ref Address.storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721_t.balance_of self owner ⇓
    inl (Simulations.erc721.balance_of storage owner)
  | state }}.
Proof.
  admit.
Admitted.

(** The simulation [get_approved] is equal. *)
Lemma run_get_approved
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (token_id : ltac:(erc721.TokenId)) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721_t.get_approved self token_id ⇓
    inl (Simulations.erc721.get_approved storage token_id)
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
  let self := Ref.mut_ref Address.storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721_t.is_approved_for_all self owner operator ⇓
    inl (Simulations.erc721.is_approved_for_all storage owner operator)
  | state }}.
Proof.
  admit.
Admitted.

Module Output.
  Record t {A : Set} : Set := {
    result : A + M.Exception;
    state : State.t;
  }.
  Arguments t : clear implicits.
End Output.

Definition lift_simulation {A : Set}
  (simulation : MS? Simulations.erc721.State.t A)
  (storage : erc721.Erc721.t) :
  Output.t A :=
  let '(result, (storage, events)) := simulation (storage, []) in
  let result :=
    match result with
    | inl result => inl result
    | inr error => inr (M.Exception.Panic error)
    end in
  {|
    Output.result := result;
    Output.state := {|
      State.storage := Some storage;
      State.events := events;
    |};
  |}.

(** The simulation [clear_approval] is equal. *)
Lemma run_clear_approval
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (token_id : ltac:(erc721.TokenId)) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  let simulation :=
    lift_simulation
      (Simulations.erc721.clear_approval token_id) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721_t.clear_approval self token_id ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.

(** The simulation [approve_for_all] is equal. *)
Lemma run_approve_for_all
    (env : erc721.Env.t)
    (storage : erc721.Erc721.t)
    (to : erc721.AccountId.t)
    (approved : bool.t) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  let simulation :=
    lift_simulation
      (Simulations.erc721.approve_for_all env to approved) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721_t.approve_for_all self to approved ⇓
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
    (approved : bool.t) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  let simulation :=
    lift_simulation
      (Simulations.erc721.set_approval_for_all env to approved) storage in
  {{ Environment.of_env env, state |
    erc721.Impl_erc721_Erc721_t.set_approval_for_all self to approved ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  admit.
Admitted.
