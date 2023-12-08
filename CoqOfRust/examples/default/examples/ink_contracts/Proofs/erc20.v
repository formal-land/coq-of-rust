Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.Proofs.M.
Require Import CoqOfRust.lib.Proofs.lib.
Require CoqOfRust.examples.default.examples.ink_contracts.Proofs.Lib.
Require CoqOfRust.examples.default.examples.ink_contracts.Simulations.erc20.
Require CoqOfRust.examples.default.examples.ink_contracts.erc20.

Import Simulations.M.Notations.

(** ** Definition of state and allocation. *)

Module State.
  Record t : Set := {
    storage : option erc20.Erc20.t;
    events : list erc20.Event.t;
  }.

  Definition of_storage (storage : erc20.Erc20.t) : t := {|
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
      | Address.storage => erc20.Erc20.t
      | Address.events => list erc20.Event.t
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
    erc20.Env.t * M.Val (list erc20.Event.t).

  Definition of_env (env : erc20.Env.t) : t :=
    (env, Ref.mut_ref Address.events).
End Environment.

Definition sum_of_money (storage : erc20.Erc20.t) : Z :=
  Lib.Mapping.sum
    Integer.to_Z
    storage.(erc20.Erc20.balances).

Module Erc20.
  Module Valid_without_sum.
    (** The storage can temporarily have a [total_supply] than is not equal to
        the sum of balances. *)
    Record t (storage : erc20.Erc20.t) : Prop := {
      total_supply :
        Integer.Valid.t storage.(erc20.Erc20.total_supply);
      balances :
        Lib.Mapping.Forall
          (fun _ balance => Integer.Valid.t balance)
          storage.(erc20.Erc20.balances);
      allowances :
        Lib.Mapping.Forall
          (fun _ balance => Integer.Valid.t balance)
          storage.(erc20.Erc20.allowances);
    }.
  End Valid_without_sum.

  Module Valid.
    Record t (storage : erc20.Erc20.t) : Prop := {
      valid_without_sum : Valid_without_sum.t storage;
      sum :
        Integer.to_Z storage.(erc20.Erc20.total_supply) =
        sum_of_money storage;
    }.
  End Valid.
End Erc20.

Module AccountId.
  Definition eqb (x y : erc20.AccountId.t) : bool :=
    x.(erc20.AccountId.x0) ==u128 y.(erc20.AccountId.x0).

  Lemma eqb_true (x y : erc20.AccountId.t) :
    eqb x y = true ->
    x = y.
  Proof.
    destruct x as [[x]], y as [[y]].
    unfold
      eqb,
      BinOp.Pure.eq,
      BinOp.Pure.make_comparison.
    cbn; intros.
    now replace x with y by lia.
  Qed.

  Lemma eqb_false (x y : erc20.AccountId.t) :
    eqb x y = false ->
    x <> y.
  Proof.
    destruct x as [[x]], y as [[y]].
    unfold
      eqb,
      BinOp.Pure.eq,
      BinOp.Pure.make_comparison.
    cbn; intros.
    intro; assert (x = y) by congruence.
    lia.
  Qed.

  Lemma eq_or_neq (x y : erc20.AccountId.t) :
    x = y \/ x <> y.
  Proof.
    destruct x as [[x]], y as [[y]].
    destruct (Z.eq_dec x y); sfirstorder.
  Qed.

  Lemma eq_or_neq_couple (x y : erc20.AccountId.t * erc20.AccountId.t) :
    x = y \/ x <> y.
  Proof.
    destruct x as [x1 x2], y as [y1 y2].
    destruct (eq_or_neq x1 y1);
      destruct (eq_or_neq x2 y2);
      hauto lq: on.
  Qed.
End AccountId.

Module Mapping.
  Lemma insert_balances_is_valid from (diff : u128.t) storage
    (H_diff : Integer.Valid.t diff)
    (H_storage : Erc20.Valid_without_sum.t storage) :
    Erc20.Valid_without_sum.t
      storage <|
        erc20.Erc20.balances :=
          Lib.Mapping.insert from diff storage.(erc20.Erc20.balances)
      |>.
  Proof.
    constructor; try apply H_storage.
    eapply Lib.Mapping.Forall_insert;
      sauto lq: on use: AccountId.eq_or_neq.
  Qed.

  Lemma insert_allowances_is_valid couple (diff : u128.t) storage
    (H_diff : Integer.Valid.t diff)
    (H_storage : Erc20.Valid.t storage) :
    Erc20.Valid.t
      storage <|
        erc20.Erc20.allowances :=
          Lib.Mapping.insert couple diff storage.(erc20.Erc20.allowances)
      |>.
  Proof.
    constructor; try apply H_storage.
    constructor; cbn; try apply H_storage.
    eapply Lib.Mapping.Forall_insert; try assumption; try apply H_storage.
    apply AccountId.eq_or_neq_couple.
  Qed.
End Mapping.

(** ** Verification of the simulations. *)

Module Env.
  (** The simulation [caller] is equal. *)
  Lemma run_caller (env : erc20.Env.t) (state : State.t) :
    let ref_env := Ref.Imm env in
    {{ Environment.of_env env, state |
      erc20.Impl_erc20_Env_t.caller ref_env ⇓
      inl (Simulations.erc20.Env.caller env)
    | state }}.
  Proof.
    run_symbolic.
  Qed.
  Opaque erc20.Impl_erc20_Env_t.caller.

  (** The simulation [emit_event] is equal. *)
  Lemma run_emit_event
    (env : erc20.Env.t)
    (event : erc20.Event.t)
    (state : State.t) :
    let ref_env := Ref.Imm env in
    {{ Environment.of_env env, state |
      erc20.Impl_erc20_Env_t.emit_event ref_env event ⇓
      inl tt
    | state <|
        State.events :=
          Simulations.erc20.Env.emit_event state.(State.events) event
      |>
    }}.
  Proof.
    run_symbolic.
  Qed.
  Opaque erc20.Impl_erc20_Env_t.emit_event.
End Env.

(** The simulation [env] is equal. *)
Lemma run_env (env : erc20.Env.t) (storage : erc20.Erc20.t) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  {{ Environment.of_env env, state |
    erc20.Impl_erc20_Erc20_t.env self ⇓
    inl (Simulations.erc20.env env)
  | state }}.
Proof.
  run_symbolic.
  eapply Run.Call. {
    run_symbolic.
  }
  run_symbolic.
Qed.
Opaque erc20.Impl_erc20_Erc20_t.env.

(** The simulation [total_supply] is equal. *)
Lemma run_total_supply
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  {{ Environment.of_env env, state |
    erc20.Impl_erc20_Erc20_t_2.total_supply self ⇓
    inl (Simulations.erc20.total_supply storage)
  | state }}.
Proof.
  unfold erc20.Impl_erc20_Erc20_t_2.total_supply.
  run_symbolic.
Qed.
Opaque erc20.Impl_erc20_Erc20_t_2.total_supply.

(** The simulation [balance_of_impl] is equal. *)
Lemma run_balance_of_impl
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  let ref_owner : ref erc20.AccountId.t := Ref.Imm owner in
  {{ Environment.of_env env, state |
    erc20.Impl_erc20_Erc20_t_2.balance_of_impl self ref_owner ⇓
    inl (Simulations.erc20.balance_of_impl storage owner)
  | state }}.
Proof.
  unfold
    erc20.Impl_erc20_Erc20_t_2.balance_of_impl,
    Simulations.erc20.balance_of_impl.
  run_symbolic.
  eapply Run.Call. {
    run_symbolic.
  }
  destruct Lib.Mapping.get; eapply Run.Call; run_symbolic.
Qed.
Opaque erc20.Impl_erc20_Erc20_t_2.balance_of_impl.

(** The simulation [balance_of_impl] is valid. *)
Lemma balance_of_impl_is_valid
  (storage : erc20.Erc20.t)
  (owner : erc20.AccountId.t)
  (H_storage : Erc20.Valid_without_sum.t storage) :
  Integer.Valid.t (Simulations.erc20.balance_of_impl storage owner).
Proof.
  unfold Simulations.erc20.balance_of_impl, Integer.Valid.t.
  destruct Lib.Mapping.get eqn:H_get; simpl.
  { lia. }
  { sauto lq: on rew: off unfold: Lib.Mapping.Forall. }
Qed.

(** The simulation [balance_of] is equal. *)
Lemma run_balance_of
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  {{ Environment.of_env env, state |
    erc20.Impl_erc20_Erc20_t_2.balance_of self owner ⇓
    inl (Simulations.erc20.balance_of storage owner)
  | state }}.
Proof.
  unfold
    erc20.Impl_erc20_Erc20_t_2.balance_of,
    Simulations.erc20.balance_of.
  run_symbolic.
  eapply Run.Call. {
    apply run_balance_of_impl.
  }
  run_symbolic.
Qed.
Opaque erc20.Impl_erc20_Erc20_t_2.balance_of.

(** The simulation [allowance_impl] is equal. *)
Lemma run_allowance_impl
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t)
    (spender : erc20.AccountId.t) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  let ref_owner : ref erc20.AccountId.t := Ref.Imm owner in
  let ref_spender : ref erc20.AccountId.t := Ref.Imm spender in
  {{ Environment.of_env env, state |
    erc20.Impl_erc20_Erc20_t_2.allowance_impl self ref_owner ref_spender ⇓
    inl (Simulations.erc20.allowance_impl storage owner spender)
  | state }}.
Proof.
  unfold
    erc20.Impl_erc20_Erc20_t_2.allowance_impl,
    Simulations.erc20.allowance_impl.
  run_symbolic.
  eapply Run.Call. {
    run_symbolic.
  }
  destruct Lib.Mapping.get; eapply Run.Call; run_symbolic.
Qed.
Opaque erc20.Impl_erc20_Erc20_t_2.allowance_impl.

Lemma allowance_impl_is_valid
  (storage : erc20.Erc20.t)
  (owner : erc20.AccountId.t)
  (spender : erc20.AccountId.t)
  (H_storage : Erc20.Valid.t storage) :
  Integer.Valid.t (Simulations.erc20.allowance_impl storage owner spender).
Proof.
  unfold Simulations.erc20.allowance_impl, Integer.Valid.t.
  destruct Lib.Mapping.get eqn:H_get; simpl.
  { lia. }
  { sauto lq: on rew: off unfold: Lib.Mapping.Forall. }
Qed.

(** The simulation [allowance] is equal. *)
Lemma run_allowance
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t)
    (spender : erc20.AccountId.t) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  {{ Environment.of_env env, state |
    erc20.Impl_erc20_Erc20_t_2.allowance self owner spender ⇓
    inl (Simulations.erc20.allowance storage owner spender)
  | state }}.
Proof.
  unfold
    erc20.Impl_erc20_Erc20_t_2.allowance,
    Simulations.erc20.allowance.
  run_symbolic.
  eapply Run.Call. {
    apply run_allowance_impl.
  }
  run_symbolic.
Qed.
Opaque erc20.Impl_erc20_Erc20_t_2.allowance.

Lemma sub_eq_optimistic (v1 v2 : u128.t) :
    Integer.Valid.t v1 ->
    Integer.Valid.t v2 ->
    v1 <u128 v2 = false ->
    BinOp.Panic.sub v1 v2 =
    M.pure (BinOp.Optimistic.sub v1 v2).
Proof.
  unfold Integer.Valid.t.
  unfold
    BinOp.Panic.sub,
    BinOp.Panic.make_arithmetic,
    BinOp.Error.make_arithmetic,
    Integer.normalize_error.
  unfold
    BinOp.Pure.lt,
    BinOp.Pure.make_comparison.
  simpl.
  intros; destruct v1, v2.
  repeat (destruct (_ <? _) eqn:? in |- *; [lia|]).
  reflexivity.
Qed.

Module Output.
  Record t {A : Set} : Set := {
    result : A + M.Exception;
    state : State.t;
  }.
  Arguments t : clear implicits.
End Output.

Definition lift_simulation {A : Set}
  (simulation : MS? Simulations.erc20.State.t A)
  (storage : erc20.Erc20.t) :
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

(** The simulation [transfer_from_to] is equal. *)
Lemma run_transfer_from_to
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance))
    (H_storage : Erc20.Valid.t storage)
    (H_value : Integer.Valid.t value) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  let ref_from : ref erc20.AccountId.t := Ref.Imm from in
  let ref_to : ref erc20.AccountId.t := Ref.Imm to in
  let simulation :=
    lift_simulation
      (Simulations.erc20.transfer_from_to from to value) storage in
  {{ Environment.of_env env, state |
    erc20.Impl_erc20_Erc20_t_2.transfer_from_to self ref_from ref_to value ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  unfold
    erc20.Impl_erc20_Erc20_t_2.transfer_from_to,
    Simulations.erc20.transfer_from_to,
    lift_simulation.
  run_symbolic.
  eapply Run.Call. {
    apply run_balance_of_impl.
  }
  run_symbolic.
  destruct (_ <u128 _) eqn:H_lt; simpl.
  { run_symbolic. }
  { run_symbolic.
    rewrite sub_eq_optimistic;
      try apply balance_of_impl_is_valid;
      try (destruct H_storage; assumption).
    run_symbolic.
    eapply Run.Call. {
      run_symbolic.
    }
    run_symbolic.
    eapply Run.Call. {
      apply run_balance_of_impl.
    }
    run_symbolic.
    unfold
      BinOp.Error.add,
      BinOp.Panic.add,
      BinOp.Panic.make_arithmetic.
    destruct BinOp.Error.make_arithmetic; run_symbolic.
    eapply Run.Call. {
      run_symbolic.
    }
    run_symbolic.
    eapply Run.Call. {
      apply run_env.
    }
    run_symbolic.
    eapply Run.Call. {
      apply Env.run_emit_event.
    }
    run_symbolic.
  }
Qed.
Opaque erc20.Impl_erc20_Erc20_t_2.transfer_from_to.

(** The simulation [transfer] is equal. *)
Lemma run_transfer
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance))
    (H_storage : Erc20.Valid.t storage)
    (H_value : Integer.Valid.t value) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  let simulation :=
    lift_simulation
      (Simulations.erc20.transfer env to value) storage in
  {{ Environment.of_env env, state |
    erc20.Impl_erc20_Erc20_t_2.transfer self to value ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  unfold erc20.Impl_erc20_Erc20_t_2.transfer,
    Simulations.erc20.transfer,
    lift_simulation.
  Opaque erc20.transfer_from_to.
  run_symbolic.
  eapply Run.Call. {
    apply run_env.
  }
  run_symbolic.
  eapply Run.Call. {
    apply Env.run_caller.
  }
  run_symbolic.
  eapply Run.Call. {
    now apply run_transfer_from_to.
  }
  unfold lift_simulation.
  destruct erc20.transfer_from_to as [[] [?storage ?logs]]; run_symbolic.
  Transparent erc20.transfer_from_to.
Qed.
Opaque erc20.Impl_erc20_Erc20_t_2.transfer.

(** The simulation [approve] is equal. *)
Lemma run_approve
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (spender : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  let simulation :=
    lift_simulation
      (Simulations.erc20.approve env spender value) storage in
  {{ Environment.of_env env, state |
    erc20.Impl_erc20_Erc20_t_2.approve self spender value ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  unfold erc20.Impl_erc20_Erc20_t_2.approve,
    Simulations.erc20.approve.
  repeat (
    eapply Run.Call ||
    run_symbolic ||
    apply run_env
  ).
Qed.
Opaque erc20.Impl_erc20_Erc20_t_2.approve.

(** The simulation [transfer_from] is equal. *)
Lemma run_transfer_from
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance))
    (H_storage : Erc20.Valid.t storage)
    (H_value : Integer.Valid.t value) :
  let state := State.of_storage storage in
  let self := Ref.mut_ref Address.storage in
  let simulation :=
    lift_simulation
      (Simulations.erc20.transfer_from env from to value) storage in
  {{ Environment.of_env env, state |
    erc20.Impl_erc20_Erc20_t_2.transfer_from self from to value ⇓
    simulation.(Output.result)
  | simulation.(Output.state) }}.
Proof.
  unfold erc20.Impl_erc20_Erc20_t_2.transfer_from,
    Simulations.erc20.transfer_from,
    lift_simulation.
  repeat (
    eapply Run.Call ||
    run_symbolic ||
    apply run_env ||
    apply run_allowance_impl
  ).
  unfold use.
  destruct (_ <u128 _) eqn:H_lt; simpl; run_symbolic.
  eapply Run.Call. {
    now apply run_transfer_from_to.
  }
  unfold lift_simulation.
  unfold M.StateError.bind.
  destruct erc20.transfer_from_to as [[[]|] [?storage ?logs]]; run_symbolic.
  { eapply Run.Call. {
      run_symbolic.
    }
    run_symbolic.
    rewrite sub_eq_optimistic;
      try apply allowance_impl_is_valid;
      try assumption.
    run_symbolic.
    eapply Run.Call. {
      run_symbolic.
    }
    run_symbolic.
  }
  { eapply Run.Call. {
      run_symbolic.
    }
    run_symbolic.
    eapply Run.Call. {
      run_symbolic.
    }
    run_symbolic.
  }
Qed.
Opaque erc20.Impl_erc20_Erc20_t_2.transfer_from.

(** ** Standalone proofs. *)

(** Starting from a state with a given [balance] for a given [owner], when we
    read that information we get the expected [balance]. *)
Lemma balance_of_impl_read_id
    (env : erc20.Env.t)
    (owner : erc20.AccountId.t)
    (balance : u128.t)
    allowances :
  let storage := {|
    erc20.Erc20.total_supply := balance;
    erc20.Erc20.balances := Lib.Mapping.insert owner balance Lib.Mapping.empty;
    erc20.Erc20.allowances := allowances;
  |} in
  (* An initial state *)
  let state := State.of_storage storage in
  (* The value [self] is allocated in the state *)
  let self : ref erc20.Erc20.t := Ref.mut_ref Address.storage in
  (* The value [owner] is an immediate value *)
  let ref_owner : ref erc20.AccountId.t := Ref.Imm owner in
  {{ Environment.of_env env, state |
    erc20.Impl_erc20_Erc20_t_2.balance_of_impl self ref_owner ⇓
    (* expected output *)
    inl balance
    (* the state does not change, there are no new logs *)
  | state }}.
Proof.
  intros.
  replace balance with (erc20.balance_of_impl storage owner).
  2: {
    unfold erc20.balance_of_impl.
    simpl.
    now rewrite Lib.Mapping.get_insert_eq.
  }
  apply run_balance_of_impl.
Qed.

(** ** Serialization of messages and global reasoning. *)

Module ReadMessage.
  (** A message that only read the store. *)
  Inductive t : Set -> Set :=
  | total_supply :
    t ltac:(erc20.Balance)
  | balance_of
    (owner : erc20.AccountId.t) :
    t ltac:(erc20.Balance)
  | allowance
    (owner : erc20.AccountId.t)
    (spender : erc20.AccountId.t) :
    t ltac:(erc20.Balance)
  .

  Definition dispatch {A : Set} (message : t A) : M A :=
    let self := Ref.mut_ref Address.storage in
    match message with
    | total_supply => erc20.Impl_erc20_Erc20_t_2.total_supply self
    | balance_of owner =>
      erc20.Impl_erc20_Erc20_t_2.balance_of self owner
    | allowance owner spender =>
      erc20.Impl_erc20_Erc20_t_2.allowance
        self
        owner
        spender
    end.

  Definition simulation_dispatch
      {A : Set}
      (env : erc20.Env.t)
      (storage : erc20.Erc20.t)
      (message : t A) :
      A :=
    match message with
    | total_supply =>
      Simulations.erc20.total_supply storage
    | balance_of owner =>
      Simulations.erc20.balance_of storage owner
    | allowance owner spender =>
      Simulations.erc20.allowance storage owner spender
    end.

  (** The simulation [simulation_dispatch] is valid. *)
  Lemma run_dispatch
      {A : Set}
      (env : erc20.Env.t)
      (storage : erc20.Erc20.t)
      (message : t A) :
    let state := State.of_storage storage in
    let simulation := simulation_dispatch env storage message in
    {{ Environment.of_env env, state |
      dispatch message ⇓
      inl simulation
    | state }}.
  Proof.
    destruct message; simpl.
    { apply run_total_supply. }
    { apply run_balance_of. }
    { apply run_allowance. }
  Qed.
End ReadMessage.

Module WriteMessage.
  (** A message that can mutate the store. *)
  Inductive t : Set :=
  | transfer
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
    t
  | approve
    (spender : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
    t
  | transfer_from
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
    t
  .

  Module Valid.
    Definition t (write_message : t) : Prop :=
      match write_message with
      | transfer _ value => Integer.Valid.t value
      | approve _ value => Integer.Valid.t value
      | transfer_from _ _ value => Integer.Valid.t value
      end.
  End Valid.

  Definition dispatch (message : t) : M ltac:(erc20.Result unit) :=
    let self := Ref.mut_ref Address.storage in
    match message with
    | transfer to value =>
      erc20.Impl_erc20_Erc20_t_2.transfer
        self
        to
        value
    | approve spender value =>
      erc20.Impl_erc20_Erc20_t_2.approve
        self
        spender
        value
    | transfer_from from to value =>
      erc20.Impl_erc20_Erc20_t_2.transfer_from
        self
        from
        to
        value
    end.

  Definition simulation_dispatch
      (env : erc20.Env.t)
      (message : t) :
      MS? Simulations.erc20.State.t ltac:(erc20.Result unit) :=
    match message with
    | transfer to value =>
      Simulations.erc20.transfer env to value
    | approve spender value =>
      Simulations.erc20.approve env spender value
    | transfer_from from to value =>
      Simulations.erc20.transfer_from env from to value
    end.

  (** The simulation [simulation_dispatch] is valid. *)
  Lemma run_dispatch
      (env : erc20.Env.t)
      (storage : erc20.Erc20.t)
      (message : t)
      (H_storage : Erc20.Valid.t storage)
      (H_message : Valid.t message) :
    let simulation :=
      lift_simulation
        (simulation_dispatch env message) storage in
    let state := State.of_storage storage in
    {{ Environment.of_env env, state |
      dispatch message ⇓
      simulation.(Output.result)
    | simulation.(Output.state) }}.
  Proof.
    destruct message; simpl.
    { apply run_transfer; scongruence. }
    { apply run_approve. }
    { apply run_transfer_from; scongruence. }
  Qed.
End WriteMessage.

(** There are no panics with read messages. *)
Lemma read_message_no_panic
    (env : erc20.Env.t)
    (message : ReadMessage.t ltac:(erc20.Balance))
    (storage : erc20.Erc20.t) :
  let state := State.of_storage storage in
  exists result,
  {{ Environment.of_env env, state |
    ReadMessage.dispatch message ⇓ inl result
  | state }}.
Proof.
  destruct message; simpl.
  { eexists.
    apply run_total_supply.
  }
  { eexists.
    apply run_balance_of.
  }
  { eexists.
    apply run_allowance.
  }
Qed.

Lemma transfer_from_to_is_valid
    (storage : erc20.Erc20.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance))
    (H_storage : Erc20.Valid.t storage)
    (H_value : Integer.Valid.t value) :
  let '(result, (storage, _)) :=
    Simulations.erc20.transfer_from_to from to value (storage, []) in
  match result with
  | inl _ => Erc20.Valid.t storage
  | _ => True
  end.
Proof.
  unfold Simulations.erc20.transfer_from_to; cbn.
  destruct (_ <u128 _) eqn:H_lt; [scongruence|]; cbn.
  match goal with
  | |- context[Lib.Mapping.insert _ ?diff_value _] =>
    set (diff := diff_value)
  end.
  assert (H_diff : Integer.Valid.t diff). {
    unfold diff; clear diff.
    unfold BinOp.Pure.lt, BinOp.Pure.make_comparison in H_lt.
    pose proof (balance_of_impl_is_valid storage from).
    sauto qb: on drew: off solve: lia.
  }
  destruct BinOp.Error.add as [sum|] eqn:H_add; [|trivial]; cbn.
  assert (H_sum : Integer.Valid.t sum). {
    eapply BinOp.Error.add_is_valid;
      try apply H_add;
      try assumption;
      try apply Integer.C.u128_valid.
    apply balance_of_impl_is_valid; try assumption.
    apply Mapping.insert_balances_is_valid; now try apply H_storage.
  }
  match goal with
  | _ : BinOp.Error.add ?v1 ?v2 = inl sum |- _ =>
    assert (H_sum_eq : sum = BinOp.Optimistic.add v1 v2)
  end. {
    unfold
      BinOp.Error.add,
      BinOp.Error.make_arithmetic,
      Integer.normalize_error
      in H_add.
    hauto lq: on rew: off.
  }
  constructor; cbn.
  { repeat (
      apply Mapping.insert_balances_is_valid ||
      assumption ||
      apply H_storage
    ).
  }
  { unfold sum_of_money; cbn.
    rewrite H_sum_eq; clear H_sum_eq.
    repeat rewrite Lib.Mapping.sum_insert.
    pose proof H_storage.(Erc20.Valid.sum _) as H_sum_eq.
    unfold sum_of_money in H_sum_eq; cbn in H_sum_eq; rewrite <- H_sum_eq.
    clear H_sum_eq.
    destruct (AccountId.eq_or_neq to from) as [H_to_from_eq | H_to_from_neq].
    { rewrite H_to_from_eq in *; clear H_to_from_eq.
      unfold erc20.balance_of_impl in *; cbn.
      rewrite Lib.Mapping.get_insert_eq; cbn.
      destruct Lib.Mapping.get; lia.
    }
    { unfold erc20.balance_of_impl in *; cbn.
      rewrite Lib.Mapping.get_insert_neq; [|assumption]; cbn.
      repeat destruct Lib.Mapping.get in |- *; lia.
    }
  }
Qed.

Lemma transfer_is_valid
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance))
    (H_storage : Erc20.Valid.t storage)
    (H_value : Integer.Valid.t value) :
  let '(result, (storage, _)) :=
    Simulations.erc20.transfer env to value (storage, []) in
  match result with
  | inl _ => Erc20.Valid.t storage
  | _ => True
  end.
Proof.
  now apply transfer_from_to_is_valid.
Qed.

Lemma approve_is_valid
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (spender : erc20.AccountId.t)
    (value : ltac:(erc20.Balance))
    (H_storage : Erc20.Valid.t storage)
    (H_value : Integer.Valid.t value) :
  let '(result, (storage, _)) :=
    Simulations.erc20.approve env spender value (storage, []) in
  Erc20.Valid.t storage.
Proof.
  cbn.
  constructor; try apply H_storage.
  unfold erc20.Env.caller; cbn.
  now apply Mapping.insert_allowances_is_valid.
Qed.

Lemma transfer_from_is_valid
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance))
    (H_storage : Erc20.Valid.t storage)
    (H_value : Integer.Valid.t value) :
  let '(result, (storage, _)) :=
    Simulations.erc20.transfer_from env from to value (storage, []) in
  match result with
  | inl _ => Erc20.Valid.t storage
  | _ => True
  end.
Proof.
  cbn.
  unfold BinOp.Pure.lt, BinOp.Pure.make_comparison; cbn.
  destruct (_ <? _) eqn:H_lt; [trivial|].
  pose proof (H_transfer :=
    transfer_from_to_is_valid storage from to value H_storage H_value).
  unfold M.StateError.bind.
  destruct Simulations.erc20.transfer_from_to
    as [[?result|?exception] [?storage ?logs]];
    [|trivial].
  destruct result; cbn; [|trivial].
  apply Mapping.insert_allowances_is_valid; try assumption.
  set (allowance := Simulations.erc20.allowance_impl _ _ _) in *.
  assert (H_allowance : Integer.Valid.t allowance). {
    now apply allowance_impl_is_valid.
  }
  destruct allowance, value.
  unfold Integer.Valid.t in *; cbn in *.
  lia.
Qed.

Lemma write_dispatch_is_valid
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (write_message : WriteMessage.t)
    (H_storage : Erc20.Valid.t storage)
    (H_write_message : WriteMessage.Valid.t write_message) :
  let state := State.of_storage storage in
  let '(result, (storage, _)) :=
    WriteMessage.simulation_dispatch env write_message (storage, []) in
  match result with
  | inl _ => Erc20.Valid.t storage
  | _ => True
  end.
Proof.
  destruct write_message; simpl.
  { now apply transfer_is_valid. }
  { now apply approve_is_valid. }
  { now apply transfer_from_is_valid. }
Qed.

(** ** The sum of money is constant. *)
Module Sum_of_money_is_constant.
  Lemma transfer_from_to_constant
      (storage : erc20.Erc20.t)
      (from : erc20.AccountId.t)
      (to : erc20.AccountId.t)
      (value : ltac:(erc20.Balance)) :
    let '(result, (storage', _)) :=
      Simulations.erc20.transfer_from_to from to value (storage, []) in
    match result with
    | inl _ =>
      storage.(erc20.Erc20.total_supply) =
      storage'.(erc20.Erc20.total_supply)
    | _ => True
    end.
  Proof.
    cbn.
    repeat (step; cbn; trivial).
  Qed.

  Lemma transfer_is_constant
      (env : erc20.Env.t)
      (storage : erc20.Erc20.t)
      (to : erc20.AccountId.t)
      (value : ltac:(erc20.Balance)) :
    let '(result, (storage', _)) :=
      Simulations.erc20.transfer env to value (storage, []) in
    match result with
    | inl _ =>
      storage.(erc20.Erc20.total_supply) =
      storage'.(erc20.Erc20.total_supply)
    | _ => True
    end.
  Proof.
    apply transfer_from_to_constant.
  Qed.

  Lemma approve_is_constant
      (env : erc20.Env.t)
      (storage : erc20.Erc20.t)
      (spender : erc20.AccountId.t)
      (value : ltac:(erc20.Balance)) :
    let '(result, (storage', _)) :=
      Simulations.erc20.approve env spender value (storage, []) in
    match result with
    | inl _ =>
      storage.(erc20.Erc20.total_supply) =
      storage'.(erc20.Erc20.total_supply)
    | _ => True
    end.
  Proof.
    reflexivity.
  Qed.

  Lemma transfer_from_is_constant
      (env : erc20.Env.t)
      (storage : erc20.Erc20.t)
      (from : erc20.AccountId.t)
      (to : erc20.AccountId.t)
      (value : ltac:(erc20.Balance)) :
    let '(result, (storage', _)) :=
      Simulations.erc20.transfer_from env from to value (storage, []) in
    match result with
    | inl _ =>
      storage.(erc20.Erc20.total_supply) =
      storage'.(erc20.Erc20.total_supply)
    | _ => True
    end.
  Proof.
    cbn.
    step; cbn; trivial.
    pose proof (transfer_from_to_constant storage from to value).
    unfold M.StateError.bind.
    destruct Simulations.erc20.transfer_from_to; cbn.
    repeat (step; cbn; trivial).
  Qed.

  Lemma write_dispatch_is_constant
      (env : erc20.Env.t)
      (storage : erc20.Erc20.t)
      (write_message : WriteMessage.t) :
    let state := State.of_storage storage in
    let '(result, (storage', _)) :=
      WriteMessage.simulation_dispatch env write_message (storage, []) in
    match result with
    | inl _ =>
      storage.(erc20.Erc20.total_supply) =
      storage'.(erc20.Erc20.total_supply)
    | _ => True
    end.
  Proof.
    destruct write_message.
    { now apply transfer_is_constant. }
    { now apply approve_is_constant. }
    { now apply transfer_from_is_constant. }
  Qed.
End Sum_of_money_is_constant.

(** ** We describe what action occured on the storage, according to the logs. *)
Module Action_from_log.
  Module Action.
    (** An action on the storage is described by a proposition relating the
        value of the storage before and after. We use a proposition rather than
        a function as there can be many possible final storage given what we
        know from the logs. *)
    Definition t : Type := erc20.Erc20.t -> erc20.Erc20.t -> Prop.
  End Action.

  (** The new value of the field [balances] of the storage after a tranfer. Here
      we ignore the overflow on integers as we consider the operation
      successful. *)
  Definition balances_of_transfer
      (storage : erc20.Erc20.t)
      (from to : erc20.AccountId.t)
      (value : ltac:(erc20.Balance)) :
      erc20.Mapping.t erc20.AccountId.t ltac:(erc20.Balance) :=
    if AccountId.eqb from to then
      (* Inserting its own value can be useful to initialize an account *)
      Lib.Mapping.insert
        from
        (Simulations.erc20.balance_of_impl storage from)
        storage.(erc20.Erc20.balances)
    else
      let from_value := Simulations.erc20.balance_of_impl storage from in
      let to_value := Simulations.erc20.balance_of_impl storage to in
      Lib.Mapping.insert from (BinOp.Optimistic.sub from_value value)
      (Lib.Mapping.insert to (BinOp.Optimistic.add to_value value)
      storage.(erc20.Erc20.balances)).

  (** The action on the storage that we can infer from an event. *)
  Definition action_of_event (event : erc20.Event.t) : Action.t :=
    fun storage storage' =>
    match event with
    | erc20.Event.Transfer (erc20.Transfer.Build_t
        (option.Option.Some from)
        (option.Option.Some to)
        value
      ) =>
      (* In case of transfer event, we do not know how the allowances are
         updated. *)
      exists allowances',
      storage' =
      storage <|
        erc20.Erc20.balances := balances_of_transfer storage from to value
      |> <|
        erc20.Erc20.allowances := allowances'
      |>
    | erc20.Event.Transfer (erc20.Transfer.Build_t _ _ _) => False
    | erc20.Event.Approval (erc20.Approval.Build_t owner spender value) =>
      storage' =
      storage <|
        erc20.Erc20.allowances :=
          Lib.Mapping.insert (owner, spender) value
            storage.(erc20.Erc20.allowances)
      |>
    end.

  (** Iterate the events. Actually, in this example, there is at most one event
      per primitive of the smart contract
      Note that we apply the events in the reverse order, as the last event is
      added last in the list, and thus appear at the head. *)
  Fixpoint action_of_events (events : list erc20.Event.t) : Action.t :=
    fun storage storage' =>
    match events with
    | [] => storage' = storage
    | event :: events =>
      exists storage_inter,
      action_of_event event storage_inter storage' /\
      action_of_events events storage storage_inter
    end.

  (** The effect on the storage of the function [transfer_from_to]. *)
  Lemma transfer_from_to_on_storage
      (storage : erc20.Erc20.t)
      (from to : erc20.AccountId.t)
      (value : ltac:(erc20.Balance)) :
    match
      Simulations.erc20.transfer_from_to from to value (storage, [])
    with
    | (inl (result.Result.Ok tt), (storage', _)) =>
      storage' =
      storage <|
        erc20.Erc20.balances := balances_of_transfer storage from to value
      |>
    | _ => True
    end.
  Proof.
    cbn.
    destruct (_ <u128 _) eqn:?; cbn; [easy|].
    unfold
      BinOp.Error.add,
      BinOp.Error.make_arithmetic,
      Integer.normalize_error.
    do 2 (destruct (_ <? _); cbn; [easy|]).
    unfold balances_of_transfer.
    destruct AccountId.eqb eqn:?.
    { replace to with from in * by (apply AccountId.eqb_true; assumption).
      set (initial_value := Simulations.erc20.balance_of_impl _ _) in *.
      unfold Simulations.erc20.balance_of_impl; cbn.
      rewrite Lib.Mapping.get_insert_eq.
      destruct storage; cbn.
      unfold RecordUpdate.set; f_equal.
      rewrite Lib.Mapping.insert_insert by apply AccountId.eq_or_neq.
      f_equal.
      destruct initial_value as [initial_value], value as [value].
      f_equal.
      lia.
    }
    { assert (from <> to) by now apply AccountId.eqb_false.
      destruct storage; cbn.
      unfold RecordUpdate.set; f_equal.
      unfold Simulations.erc20.balance_of_impl in *; cbn in *.
      rewrite Lib.Mapping.get_insert_neq by congruence.
      set (from_value := Lib.Mapping.get from _) in *.
      set (to_value := Lib.Mapping.get to _) in *.
      destruct
        from_value as [|[from_value]],
        to_value as [|[to_value]],
        value as [value].
      all: rewrite Lib.Mapping.insert_switch;
        try apply AccountId.eq_or_neq;
        try congruence.
    }
  Qed.

  (** The logs of the function [transfer_from_to]. *)
  Lemma event_from_transfer_from_to
      (storage : erc20.Erc20.t)
      (from to : erc20.AccountId.t)
      (value : ltac:(erc20.Balance)) :
    match
      Simulations.erc20.transfer_from_to from to value (storage, [])
    with
    | (inl (result.Result.Ok tt), (_, events)) =>
      let event := erc20.Event.Transfer {|
        erc20.Transfer.from := option.Option.Some from;
        erc20.Transfer.to := option.Option.Some to;
        erc20.Transfer.value := value;
      |} in
      [event] = events
    | _ => True
    end.
  Proof.
    cbn.
    destruct (_ <u128 _); cbn; [easy|].
    now destruct BinOp.Error.add.
  Qed.

  (** We show that the action that we infer from the logs is indeed what is
      happening on the storage. *)
  Lemma retrieve_action_from_logs
      (env : erc20.Env.t)
      (storage : erc20.Erc20.t)
      (write_message : WriteMessage.t)
      (events : list erc20.Event.t) :
    match
      WriteMessage.simulation_dispatch env write_message (storage, [])
    with
    | (inl (result.Result.Ok tt), (storage', events)) =>
      action_of_events events storage storage'
    | _ => True
    end.
  Proof.
    Opaque Simulations.erc20.transfer_from_to.
    destruct write_message; cbn;
      unfold Simulations.erc20.transfer, M.StateError.bind;
      try (destruct (_ <u128 _) eqn:?; cbn; [easy|]);
      try match goal with
      | |- context[erc20.transfer_from_to ?from ?to ?value (?storage, [])] =>
        pose proof (
          transfer_from_to_on_storage storage from to value
        );
        pose proof (
          event_from_transfer_from_to storage from to value
        )
      end;
      try destruct Simulations.erc20.transfer_from_to
        as [[[[]|?error]|?exception] [?storage ?events]];
      hauto l: on.
    Transparent Simulations.erc20.transfer_from_to.
  Qed.
End Action_from_log.

(** One can only change its own allowance using the [approve] method. *)
Lemma approve_only_changes_owner_allowance
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (spender : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
  let '(result, (storage', _)) :=
    Simulations.erc20.approve env spender value (storage, []) in
  match result with
  | inl (result.Result.Ok tt) =>
    forall owner spender,
    Integer.to_Z (Simulations.erc20.allowance storage' owner spender) <>
      Integer.to_Z (Simulations.erc20.allowance storage owner spender) ->
    owner = Simulations.erc20.Env.caller env
  | _ => True
  end.
Proof.
  unfold erc20.allowance, erc20.allowance_impl; cbn.
  intros.
  match goal with
  | _ : context[Lib.Mapping.get ?key1 (Lib.Mapping.insert ?key2 _ _)] |- _ =>
    destruct (AccountId.eq_or_neq_couple key1 key2) as [H_eq | H_neq]
  end.
  { sfirstorder. }
  { rewrite Lib.Mapping.get_insert_neq in * by assumption.
    destruct Lib.Mapping.get; lia.
  }
Qed.
