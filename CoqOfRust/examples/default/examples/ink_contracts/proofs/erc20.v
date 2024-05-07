Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.proofs.M.
Require Import CoqOfRust.simulations.M.
Require Import CoqOfRust.lib.proofs.lib.
Require CoqOfRust.core.convert.mod.
Require CoqOfRust.core.default.
Require CoqOfRust.core.result.
Require CoqOfRust.core.proofs.option.
Require CoqOfRust.core.simulations.result.
Require CoqOfRust.examples.default.examples.ink_contracts.proofs.lib.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.erc20.
Require Import CoqOfRust.examples.default.examples.ink_contracts.erc20.

Import simulations.M.Notations.
Import Run.

Definition sum_of_money (storage : erc20.Erc20.t) : Z :=
  simulations.lib.Mapping.sum id storage.(erc20.Erc20.balances).

Module Balance.
  Module Valid.
    Definition t (x : erc20.Balance.t) : Prop :=
      Integer.Valid.t Integer.U128 x.
  End Valid.

  Lemma run_Default : default.Default.TraitHasRun erc20.Balance.t (Ty.path "u128").
  Proof.
    constructor.
    eexists; split.
    { unfold IsTraitMethod.
      eexists; split.
      { cbn.
        apply core.default.default.Impl_core_default_Default_for_u128.Implements.
      }
      { reflexivity. }
    }
    { unfold Run.pure; intros.
      run_symbolic.
    }
  Qed.
End Balance.

Module Erc20.
  Module Valid_without_sum.
    (** The storage can temporarily have a [total_supply] than is not equal to
        the sum of balances. *)
    Record t (storage : erc20.Erc20.t) : Prop := {
      total_supply :
        Balance.Valid.t storage.(erc20.Erc20.total_supply);
      balances :
        lib.Mapping.Forall
          (fun _ balance => Balance.Valid.t balance)
          storage.(erc20.Erc20.balances);
      allowances :
        lib.Mapping.Forall
          (fun _ balance => Balance.Valid.t balance)
          storage.(erc20.Erc20.allowances);
    }.
  End Valid_without_sum.

  Module Valid.
    Record t (storage : erc20.Erc20.t) : Prop := {
      valid_without_sum : Valid_without_sum.t storage;
      sum : storage.(erc20.Erc20.total_supply) = sum_of_money storage;
    }.
  End Valid.

  Module SubPointer.
    Lemma get_total_supply_is_valid :
      SubPointer.Runner.Valid.t simulations.erc20.Erc20.SubPointer.get_total_supply.
    Proof.
      hauto l: on.
    Qed.

    Lemma get_balances_is_valid :
      SubPointer.Runner.Valid.t simulations.erc20.Erc20.SubPointer.get_balances.
    Proof.
      hauto l: on.
    Qed.

    Lemma get_allowances_is_valid :
      SubPointer.Runner.Valid.t simulations.erc20.Erc20.SubPointer.get_allowances.
    Proof.
      hauto l: on.
    Qed.
  End SubPointer.
End Erc20.

Module AccountId.
  Lemma eq_or_neq (x y : erc20.AccountId.t) :
    x = y \/ x <> y.
  Proof.
    destruct x as [x], y as [y].
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
  Lemma insert_balances_is_valid from diff storage
    (H_diff : Balance.Valid.t diff)
    (H_storage : Erc20.Valid_without_sum.t storage) :
    Erc20.Valid_without_sum.t
      storage <|
        erc20.Erc20.balances :=
          simulations.lib.Mapping.insert
            from diff storage.(erc20.Erc20.balances)
      |>.
  Proof.
    constructor; try apply H_storage.
    eapply lib.Mapping.Forall_insert;
      sauto lq: on use: AccountId.eq_or_neq.
  Qed.

  Lemma insert_allowances_is_valid couple diff storage
    (H_diff : Balance.Valid.t diff)
    (H_storage : Erc20.Valid.t storage) :
    Erc20.Valid.t
      storage <|
        erc20.Erc20.allowances :=
          simulations.lib.Mapping.insert
            couple diff storage.(erc20.Erc20.allowances)
      |>.
  Proof.
    constructor; try apply H_storage.
    constructor; cbn; try apply H_storage.
    eapply lib.Mapping.Forall_insert; try assumption; try apply H_storage.
    apply AccountId.eq_or_neq_couple.
  Qed.
End Mapping.

Module MState.
  Module Valid.
    Record t (x : erc20.MState.t) : Prop := {
      storage : erc20.Erc20.Valid.t x.(erc20.MState.storage);
    }.
  End Valid.
End MState.

(** ** Definition of state and allocation. *)

Module State.
  Record t : Set := {
    storage : option erc20.Erc20.t;
    events : list erc20.Event.t;
  }.

  Definition of_mstate (x : erc20.MState.t) : t :=
    {|
      storage := Some x.(erc20.MState.storage);
      events := x.(erc20.MState.events);
    |}.

  Lemma of_mstate_storage_eq (x : erc20.MState.t) (y : erc20.Erc20.t) :
    (of_mstate x) <| storage := Some y |> =
    of_mstate (x <| erc20.MState.storage := y |>).
  Proof.
    reflexivity.
  Qed.
End State.

Module Address.
  Inductive t : Set :=
  | storage : t
  | events : t.
End Address.

Module StateInstance.
  Global Instance I : State.Trait erc20.State.t Address.t := {
    get_Set address :=
      match address with
      | Address.storage => erc20.Erc20.t
      | Address.events => list erc20.Event.t
      end;
    State.read address state :=
      match address with
      | Address.storage => state.(erc20.State.storage)
      | Address.events => Some state.(erc20.State.events)
      end;
    State.alloc_write address state value :=
      match address, value with
      | Address.storage, storage =>
        Some (state <| erc20.State.storage := Some storage |>)
      | Address.events, events =>
        Some (state <| erc20.State.events := events |>)
      end;
  }.

  Lemma is_valid : M.State.Valid.t I.
    sauto.
  Qed.
End StateInstance.

(** Here the module [Env] is both the name for the environment that we use in all our simulations,
    and the name of a module in the Rust code that we are verifying. *)
Module Env.
  Definition to_value (env : erc20.Env.t) : Value.t :=
    Value.Tuple [
      φ env;
      Value.Pointer (Pointer.mutable Address.events φ)
    ].

  (** ** Verification of the simulations. *)

  (** The simulation [caller] is equal. *)
  Lemma run_caller (env : erc20.Env.t) (state : State.t) :
    let ref_env :=
      Value.Pointer (Pointer.Immediate (φ env)) in
    {{ env, Env.to_value, state |
      erc20.Impl_erc20_Env.caller [] [ref_env] ⇓
      inl (φ (simulations.erc20.Env.caller env))
    | state }}.
  Proof.
    run_symbolic.
  Qed.
  Opaque erc20.Impl_erc20_Env.caller.

  (** The simulation [emit_event] is equal. *)
  Lemma run_emit_event
    (env : erc20.Env.t)
    (event : erc20.Event.t)
    (state : erc20.State.t) :
    let ref_env :=
      Value.Pointer (Pointer.Immediate (φ env)) in
    {{ env, Env.to_value, state |
      erc20.Impl_erc20_Env.emit_event [] [ref_env; φ event] ⇓
      inl (Value.Tuple [])
    | state <|
        erc20.State.events :=
          simulations.erc20.Env.emit_event state.(erc20.State.events) event
      |>
    }}.
  (* This function is axiomatized in the source. *)
  Admitted.
End Env.

(** The simulation [init_env] is equal. *)
Lemma run_init_env (env : erc20.Env.t) (state : erc20.State.t) :
  {{ env, Env.to_value, state |
    erc20.Impl_erc20_Erc20.init_env [] [] ⇓
    inl (φ (simulations.erc20.init_env env))
  | state }}.
Proof.
(* This function is axiomatized in the source. *)
Admitted.

(** The simulation [env] is equal. *)
Lemma run_env (env : erc20.Env.t) (state : erc20.State.t) :
  let self := Value.Pointer (Pointer.mutable Address.storage φ) in
  {{ env, Env.to_value, state |
    erc20.Impl_erc20_Erc20.env [] [self] ⇓
    inl (φ (simulations.erc20.env env))
  | state }}.
Proof.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Erc20.AssociatedFunction_init_env.
  }
  eapply Run.CallClosure. {
    apply run_init_env.
  }
  run_symbolic.
Qed.
Opaque erc20.Impl_erc20_Erc20.env.

(** The simulation [total_supply] is equal. *)
Lemma run_total_supply
    (env : erc20.Env.t)
    (state : erc20.MState.t) :
  let self := Value.Pointer (Pointer.mutable Address.storage φ) in
  {{ env, Env.to_value, State.of_mstate state |
    erc20.Impl_erc20_Erc20.total_supply [] [self] ⇓
    inl (φ (simulations.erc20.total_supply state.(erc20.MState.storage)))
  | State.of_mstate state }}.
Proof.
  unfold erc20.Impl_erc20_Erc20.total_supply.
  run_symbolic.
  apply (SubPointer.run Erc20.SubPointer.get_total_supply_is_valid); [reflexivity|].
  run_symbolic.
Qed.
Opaque erc20.Impl_erc20_Erc20.total_supply.

(** The simulation [balance_of_impl] is equal. *)
Lemma run_balance_of_impl
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (owner : erc20.AccountId.t) :
  let self := Value.Pointer (Pointer.mutable Address.storage φ) in
  let ref_owner :=
    Value.Pointer (Pointer.Immediate (φ owner)) in
  {{ env, Env.to_value, State.of_mstate state |
    erc20.Impl_erc20_Erc20.balance_of_impl [] [self; ref_owner] ⇓
    inl (φ (simulations.erc20.balance_of_impl
      state.(erc20.MState.storage)
      owner
    ))
  | State.of_mstate state }}.
Proof.
  Opaque φ.
  unfold
    erc20.Impl_erc20_Erc20.balance_of_impl,
    simulations.erc20.balance_of_impl.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply core.option.option.Impl_core_option_Option_T.AssociatedFunction_unwrap_or_default.
  }
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply lib.Impl_Mapping_t_K_V.AssociatedFunction_get.
  }
  eapply (SubPointer.run Erc20.SubPointer.get_balances_is_valid); [reflexivity|].
  eapply Run.CallClosure. {
    run_symbolic.
  }
  rewrite proofs.lib.Mapping.run_get.
  eapply Run.CallClosure. {
    apply core.proofs.option.Impl_Option_T.run_unwrap_or_default.
    apply Balance.run_Default.
  }
  run_symbolic.
  Transparent φ.
Qed.
Opaque erc20.Impl_erc20_Erc20.balance_of_impl.

(** The simulation [balance_of_impl] is valid. *)
Lemma balance_of_impl_is_valid
  (state : erc20.MState.t)
  (owner : erc20.AccountId.t)
  (H_storage : Erc20.Valid_without_sum.t state.(erc20.MState.storage)) :
  Balance.Valid.t (simulations.erc20.balance_of_impl state.(erc20.MState.storage) owner).
Proof.
  destruct state; intros.
  unfold simulations.erc20.balance_of_impl, Balance.Valid.t, Integer.Valid.t.
  destruct simulations.lib.Mapping.get eqn:H_get; cbn.
  { destruct H_storage.
    unfold lib.Mapping.Forall in *.
    sauto q: on.
  }
  { lia. }
Qed.

(** The simulation [balance_of] is equal. *)
Lemma run_balance_of
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (owner : erc20.AccountId.t) :
  let self := Value.Pointer (Pointer.mutable Address.storage φ) in
  {{ env, Env.to_value, State.of_mstate state |
    erc20.Impl_erc20_Erc20.balance_of [] [self; φ owner] ⇓
    inl (φ (simulations.erc20.balance_of state.(erc20.MState.storage) owner))
  | State.of_mstate state }}.
Proof.
  unfold
    erc20.Impl_erc20_Erc20.balance_of,
    simulations.erc20.balance_of.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Erc20.AssociatedFunction_balance_of_impl.
  }
  eapply Run.CallClosure. {
    apply run_balance_of_impl.
  }
  run_symbolic.
Qed.
Opaque erc20.Impl_erc20_Erc20.balance_of.

(** The simulation [allowance_impl] is equal. *)
Lemma run_allowance_impl
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (owner : erc20.AccountId.t)
    (spender : erc20.AccountId.t) :
  let self := Value.Pointer (Pointer.mutable Address.storage φ) in
  let ref_owner := Value.Pointer (Pointer.Immediate (φ owner)) in
  let ref_spender := Value.Pointer (Pointer.Immediate (φ spender)) in
  {{ env, Env.to_value, State.of_mstate state |
    erc20.Impl_erc20_Erc20.allowance_impl [] [self; ref_owner; ref_spender] ⇓
    inl (φ (simulations.erc20.allowance_impl
      state.(erc20.MState.storage)
      owner
      spender
    ))
  | State.of_mstate state }}.
Proof.
  Opaque φ.
  unfold
    erc20.Impl_erc20_Erc20.allowance_impl,
    simulations.erc20.allowance_impl.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply core.option.option.Impl_core_option_Option_T.AssociatedFunction_unwrap_or_default.
  }
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply lib.Impl_Mapping_t_K_V.AssociatedFunction_get.
  }
  apply (SubPointer.run Erc20.SubPointer.get_allowances_is_valid); [reflexivity|].
  run_symbolic.
  eapply Run.CallClosure. {
    run_symbolic.
  }
  eapply Run.CallClosure. {
    replace (Value.Tuple _) with (φ (owner, spender)) by reflexivity.
    rewrite proofs.lib.Mapping.run_get.
    apply core.proofs.option.Impl_Option_T.run_unwrap_or_default.
    apply Balance.run_Default.
  }
  run_symbolic.
  Transparent φ.
Qed.
Opaque erc20.Impl_erc20_Erc20.allowance_impl.

Lemma allowance_impl_is_valid
  (state : erc20.MState.t)
  (owner : erc20.AccountId.t)
  (spender : erc20.AccountId.t)
  (H_storage : Erc20.Valid.t state.(erc20.MState.storage)) :
  Balance.Valid.t (simulations.erc20.allowance_impl
    state.(erc20.MState.storage)
    owner
    spender
  ).
Proof.
  unfold simulations.erc20.allowance_impl, Balance.Valid.t, Integer.Valid.t.
  destruct simulations.lib.Mapping.get eqn:H_get; simpl.
  { destruct H_storage, valid_without_sum.
    unfold lib.Mapping.Forall in *.
    sauto.
  }
  { lia. }
Qed.

(** The simulation [allowance] is equal. *)
Lemma run_allowance
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (owner : erc20.AccountId.t)
    (spender : erc20.AccountId.t) :
  let self := Value.Pointer (Pointer.mutable Address.storage φ) in
  {{ env, Env.to_value, State.of_mstate state |
    erc20.Impl_erc20_Erc20.allowance [] [self; φ owner; φ spender] ⇓
    inl (φ (simulations.erc20.allowance
      state.(erc20.MState.storage)
      owner
      spender
    ))
  | State.of_mstate state }}.
Proof.
  unfold
    erc20.Impl_erc20_Erc20.allowance,
    simulations.erc20.allowance.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Erc20.AssociatedFunction_allowance_impl.
  }
  eapply Run.CallClosure. {
    apply run_allowance_impl.
  }
  run_symbolic.
Qed.
Opaque erc20.Impl_erc20_Erc20.allowance.

Lemma sub_eq_optimistic (v1 v2 : Z) :
    Integer.Valid.t Integer.U128 v1 ->
    Integer.Valid.t Integer.U128 v2 ->
    v1 <? v2 = false ->
    let v1 := Value.Integer v1 in
    let v2 := Value.Integer v2 in
    BinOp.Panic.make_arithmetic Z.sub Integer.U128 v1 v2 =
    M.pure (BinOp.Optimistic.sub v1 v2).
Proof.
  unfold Integer.Valid.t.
  repeat (
    unfold
      BinOp.Panic.make_arithmetic,
      Integer.normalize_with_error;
    cbn
  ).
  intros.
  repeat (destruct (_ <? _) eqn:? in |- *; [lia|]).
  reflexivity.
Qed.

Module Output.
  Record t : Set := {
    result : Value.t + Exception.t;
    state : erc20.MState.t;
  }.
End Output.

Definition lift_simulation {A : Set} `{ToValue A}
    (simulation : MS? erc20.MState.t string A)
    (state : erc20.MState.t) :
    Output.t :=
  let '(result, state) := simulation state in
  let result :=
    match result with
    | inl result => inl (φ result)
    | inr error => inr (M.Exception.Panic error)
    end in
  {|
    Output.result := result;
    Output.state := state;
  |}.

(** The simulation [transfer_from_to] is equal. *)
Lemma run_transfer_from_to
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t)
    (H_storage : Erc20.Valid.t state.(erc20.MState.storage))
    (H_value : Balance.Valid.t value) :
  let self := Value.Pointer (Pointer.mutable Address.storage φ) in
  let ref_from := Value.Pointer (Pointer.Immediate (φ from)) in
  let ref_to := Value.Pointer (Pointer.Immediate (φ to)) in
  let simulation :=
    lift_simulation
      (simulations.erc20.transfer_from_to from to value)
      state in
  {{ env, Env.to_value, State.of_mstate state |
    erc20.Impl_erc20_Erc20.transfer_from_to [] [self; ref_from; ref_to; φ value] ⇓
    simulation.(Output.result)
  | State.of_mstate simulation.(Output.state) }}.
Proof.
  unfold
    erc20.Impl_erc20_Erc20.transfer_from_to,
    simulations.erc20.transfer_from_to,
    lift_simulation.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Erc20.AssociatedFunction_balance_of_impl.
  }
  eapply Run.CallClosure. {
    apply run_balance_of_impl.
  }
  run_symbolic.
  destruct (_ <? _) eqn:H_lt; cbn.
  { run_symbolic. }
  { run_symbolic.
    eapply Run.CallPrimitiveGetAssociatedFunction. {
      apply lib.Impl_Mapping_t_K_V.AssociatedFunction_insert.
    }
    rewrite sub_eq_optimistic; trivial.
    2: {
      apply balance_of_impl_is_valid.
      apply H_storage.
    }
    run_symbolic.
    apply (SubPointer.run Erc20.SubPointer.get_balances_is_valid); [reflexivity|].
    eapply Run.CallClosure. {
      run_symbolic.
      rewrite <- proofs.lib.Mapping.run_insert.
      reflexivity.
    }
    rewrite State.of_mstate_storage_eq.
    run_symbolic.
    eapply Run.CallPrimitiveGetAssociatedFunction. {
      apply erc20.Impl_erc20_Erc20.AssociatedFunction_balance_of_impl.
    }
    eapply Run.CallClosure. {
      apply run_balance_of_impl.
    }
    run_symbolic.
    eapply Run.CallPrimitiveGetAssociatedFunction. {
      apply lib.Impl_Mapping_t_K_V.AssociatedFunction_insert.
    }
    apply (SubPointer.run Erc20.SubPointer.get_balances_is_valid); [reflexivity|].
    unfold
      BinOp.Panic.add,
      BinOp.Panic.make_arithmetic,
      BinOp.Error.make_arithmetic.
    cbn.
    destruct Integer.normalize_with_error as [sum|]; run_symbolic.
    eapply Run.CallClosure. {
      run_symbolic.
      set (map_from := simulations.lib.Mapping.insert from _ _).
      rewrite <- proofs.lib.Mapping.run_insert; f_equal.
      reflexivity.
    }
    rewrite State.of_mstate_storage_eq.
    run_symbolic.
    eapply Run.CallPrimitiveGetAssociatedFunction. {
      apply erc20.Impl_erc20_Env.AssociatedFunction_emit_event.
    }
    eapply Run.CallPrimitiveGetAssociatedFunction. {
      apply erc20.Impl_erc20_Erc20.AssociatedFunction_env.
    }
    eapply Run.CallClosure. {
      apply run_env.
    }
    run_symbolic.
    eapply Run.CallClosure. {
      evar (event : erc20.Event.t).
      set (event_value := Value.StructTuple "erc20::Event::Transfer" _).
      assert (H : φ event = event_value). {
        unfold event, event_value; cbn.
        instantiate (1 := erc20.Event.Transfer _); cbn.
        instantiate (1 := erc20.Transfer.Build_t _ _ _); cbn.
        repeat f_equal; now instantiate (1 := Some _).
      }
      rewrite <- H.
      apply Env.run_emit_event.
    }
    run_symbolic.
  }
Qed.
Opaque erc20.Impl_erc20_Erc20.transfer_from_to.

(** The simulation [transfer] is equal. *)
Lemma run_transfer
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t)
    (H_state : MState.Valid.t state)
    (H_value : Balance.Valid.t value) :
  let self := Value.Pointer (Pointer.mutable Address.storage φ) in
  let simulation :=
    lift_simulation
      (simulations.erc20.transfer env to value) state in
  {{ env, Env.to_value, State.of_mstate state |
    erc20.Impl_erc20_Erc20.transfer [] [self; φ to; φ value] ⇓
    simulation.(Output.result)
  | State.of_mstate simulation.(Output.state) }}.
Proof.
  unfold erc20.Impl_erc20_Erc20.transfer,
    simulations.erc20.transfer,
    lift_simulation.
  Opaque erc20.transfer_from_to.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Env.AssociatedFunction_caller.
  }
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Erc20.AssociatedFunction_env.
  }
  eapply Run.CallClosure. {
    apply run_env.
  }
  run_symbolic.
  eapply Run.CallClosure. {
    apply Env.run_caller.
  }
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Erc20.AssociatedFunction_transfer_from_to.
  }
  eapply Run.CallClosure. {
    apply run_transfer_from_to; sauto lq: on.
  }
  unfold lift_simulation.
  destruct erc20.transfer_from_to as [[] [?storage ?logs]]; run_symbolic.
  Transparent erc20.transfer_from_to.
Qed.
Opaque erc20.Impl_erc20_Erc20.transfer.

(** The simulation [approve] is equal. *)
Lemma run_approve
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (spender : erc20.AccountId.t)
    (value : erc20.Balance.t) :
  let self := Value.Pointer (Pointer.mutable Address.storage φ) in
  let simulation :=
    lift_simulation
      (simulations.erc20.approve env spender value) state in
  {{ env, Env.to_value, State.of_mstate state |
    erc20.Impl_erc20_Erc20.approve [] [self; φ spender; φ value] ⇓
    simulation.(Output.result)
  | State.of_mstate simulation.(Output.state) }}.
Proof.
  unfold
    erc20.Impl_erc20_Erc20.approve,
    simulations.erc20.approve.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Env.AssociatedFunction_caller.
  }
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Erc20.AssociatedFunction_env.
  }
  eapply Run.CallClosure. {
    apply run_env.
  }
  run_symbolic.
  eapply Run.CallClosure. {
    apply Env.run_caller.
  }
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply lib.Impl_Mapping_t_K_V.AssociatedFunction_insert.
  }
  apply (SubPointer.run Erc20.SubPointer.get_allowances_is_valid); [reflexivity|].
  eapply Run.CallClosure. {
    run_symbolic.
    rewrite <- proofs.lib.Mapping.run_insert; f_equal; try reflexivity.
    now instantiate (1 := (_, _)).
  }
  rewrite State.of_mstate_storage_eq.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Env.AssociatedFunction_emit_event.
  }
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Erc20.AssociatedFunction_env.
  }
  eapply Run.CallClosure. {
    apply run_env.
  }
  run_symbolic.
  eapply Run.CallClosure. {
    evar (event : erc20.Event.t).
    set (event_value := Value.StructTuple "erc20::Event::Approval" _).
    assert (H : φ event = event_value). {
      unfold event, event_value; cbn.
      instantiate (1 := erc20.Event.Approval _); cbn.
      instantiate (1 := erc20.Approval.Build_t _ _ _); cbn.
      reflexivity.
    }
    rewrite <- H.
    apply Env.run_emit_event.
  }
  run_symbolic.
Qed.
Opaque erc20.Impl_erc20_Erc20.approve.

(** The simulation [transfer_from] is equal. *)
Lemma run_transfer_from
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t)
    (H_state : MState.Valid.t state)
    (H_value : Balance.Valid.t value) :
  let self := Value.Pointer (Pointer.mutable Address.storage φ) in
  let simulation :=
    lift_simulation
      (simulations.erc20.transfer_from env from to value) state in
  {{ env, Env.to_value, State.of_mstate state |
    erc20.Impl_erc20_Erc20.transfer_from [] [self; φ from; φ to; φ value] ⇓
    simulation.(Output.result)
  | State.of_mstate simulation.(Output.state) }}.
Proof.
  unfold erc20.Impl_erc20_Erc20.transfer_from,
    simulations.erc20.transfer_from,
    lift_simulation.
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Env.AssociatedFunction_caller.
  }
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Erc20.AssociatedFunction_env.
  }
  eapply Run.CallClosure. {
    apply run_env.
  }
  run_symbolic.
  eapply Run.CallClosure. {
    apply Env.run_caller.
  }
  run_symbolic.
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Erc20.AssociatedFunction_allowance_impl.
  }
  eapply Run.CallClosure. {
    apply run_allowance_impl.
  }
  run_symbolic.
  destruct (_ <? _) eqn:H_lt; cbn; run_symbolic.
  eapply Run.CallPrimitiveGetTraitMethod. {
    eexists; split.
    { apply
        core.result.result.Impl_core_ops_try_trait_Try_for_core_result_Result_T_E.Implements.
    }
    { reflexivity. }
  }
  eapply Run.CallPrimitiveGetAssociatedFunction. {
    apply erc20.Impl_erc20_Erc20.AssociatedFunction_transfer_from_to.
  }
  eapply Run.CallClosure. {
    apply run_transfer_from_to; sauto lq: on.
  }
  unfold lift_simulation, M.StateError.bind.
  destruct erc20.transfer_from_to as [[[]| ?panic_message] [?storage ?logs]] eqn:?; run_symbolic.
  { eapply Run.CallClosure. {
      run_symbolic.
    }
    run_symbolic.
    eapply Run.CallPrimitiveGetAssociatedFunction. {
      apply lib.Impl_Mapping_t_K_V.AssociatedFunction_insert.
    }
    apply (SubPointer.run Erc20.SubPointer.get_allowances_is_valid); [reflexivity|].
    rewrite sub_eq_optimistic; try assumption.
    2: {
      apply allowance_impl_is_valid.
      sauto lq: on rew: off.
    }
    run_symbolic.
    eapply Run.CallClosure. {
      run_symbolic.
      rewrite <- proofs.lib.Mapping.run_insert.
      f_equal; cbn.
      now instantiate (1 := (_, _)).
    }
    rewrite State.of_mstate_storage_eq.
    run_symbolic.
  }
  { eapply Run.CallClosure. {
      run_symbolic.
    }
    run_symbolic.
    eapply Run.CallPrimitiveGetTraitMethod. {
      eexists; split.
      { apply
          core.result.result.Impl_core_ops_try_trait_FromResidual_where_core_convert_From_F_E_core_result_Result_core_convert_Infallible_E_for_core_result_Result_T_F.Implements.
      }
      { reflexivity. }
    }
    eapply Run.CallClosure. {
      run_symbolic.
      eapply Run.CallPrimitiveGetTraitMethod. {
        eexists; split.
        { apply core.convert.mod.convert.Impl_core_convert_From_T_for_T.Implements. }
        { reflexivity. }
      }
      eapply Run.CallClosure. {
        run_symbolic.
      }
      run_symbolic.
    }
    run_symbolic.
  }
Qed.
Opaque erc20.Impl_erc20_Erc20.transfer_from.

(** ** Serialization of messages and global reasoning. *)

Module ReadMessage.
  (** A message that only read the store. *)
  Inductive t : Set :=
  | total_supply
  | balance_of (owner : erc20.AccountId.t)
  | allowance (owner : erc20.AccountId.t) (spender : erc20.AccountId.t)
  .

  Definition dispatch (message : t) : M :=
    let self := Value.Pointer (Pointer.mutable Address.storage φ) in
    match message with
    | total_supply => erc20.Impl_erc20_Erc20.total_supply [] [self]
    | balance_of owner =>
      erc20.Impl_erc20_Erc20.balance_of [] [self; φ owner]
    | allowance owner spender =>
      erc20.Impl_erc20_Erc20.allowance [] [self; φ owner; φ spender]
    end.

  Definition simulation_dispatch
      (env : erc20.Env.t)
      (state : erc20.MState.t)
      (message : t) :
      erc20.Balance.t :=
    match message with
    | total_supply =>
      simulations.erc20.total_supply state.(erc20.MState.storage)
    | balance_of owner =>
      simulations.erc20.balance_of state.(erc20.MState.storage) owner
    | allowance owner spender =>
      simulations.erc20.allowance state.(erc20.MState.storage) owner spender
    end.

  (** The simulation [simulation_dispatch] is valid. *)
  Lemma run_dispatch
      (env : erc20.Env.t)
      (state : erc20.MState.t)
      (message : t) :
    let simulation := simulation_dispatch env state message in
    {{ env, Env.to_value, State.of_mstate state |
      dispatch message ⇓
      inl (φ simulation)
    | State.of_mstate state }}.
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
    (value : erc20.Balance.t)
  | approve
    (spender : erc20.AccountId.t)
    (value : erc20.Balance.t)
  | transfer_from
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t)
  .

  Module Valid.
    Definition t (write_message : t) : Prop :=
      match write_message with
      | transfer _ value => Balance.Valid.t value
      | approve _ value => Balance.Valid.t value
      | transfer_from _ _ value => Balance.Valid.t value
      end.
  End Valid.

  Definition dispatch (message : t) : M :=
    let self := Value.Pointer (Pointer.mutable Address.storage φ) in
    match message with
    | transfer to value =>
      erc20.Impl_erc20_Erc20.transfer [] [self; φ to; φ value]
    | approve spender value =>
      erc20.Impl_erc20_Erc20.approve [] [self; φ spender; φ value]
    | transfer_from from to value =>
      erc20.Impl_erc20_Erc20.transfer_from [] [self; φ from; φ to; φ value]
    end.

  Definition simulation_dispatch
      (env : erc20.Env.t)
      (message : t) :
      MS? erc20.MState.t string (erc20.Result.t unit) :=
    match message with
    | transfer to value =>
      simulations.erc20.transfer env to value
    | approve spender value =>
      simulations.erc20.approve env spender value
    | transfer_from from to value =>
      simulations.erc20.transfer_from env from to value
    end.

  (** The simulation [simulation_dispatch] is valid. *)
  Lemma run_dispatch
      (env : erc20.Env.t)
      (state : erc20.MState.t)
      (message : t)
      (H_state : MState.Valid.t state)
      (H_message : Valid.t message) :
    let simulation :=
      lift_simulation
        (simulation_dispatch env message) state in
    {{ env, Env.to_value, State.of_mstate state |
      dispatch message ⇓
      simulation.(Output.result)
    | State.of_mstate simulation.(Output.state) }}.
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
    (message : ReadMessage.t)
    (state : erc20.MState.t) :
  exists result,
  {{ env, Env.to_value, State.of_mstate state |
    ReadMessage.dispatch message ⇓ inl result
  | State.of_mstate state }}.
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
    (state : erc20.MState.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t)
    (H_state : MState.Valid.t state)
    (H_value : Balance.Valid.t value) :
  let '(result, state) :=
    simulations.erc20.transfer_from_to from to value state in
  match result with
  | inl _ => MState.Valid.t state
  | _ => True
  end.
Proof.
  unfold simulations.erc20.transfer_from_to; cbn.
  destruct (_ <? _) eqn:H_lt; [scongruence|]; cbn.
  match goal with
  | |- context[simulations.lib.Mapping.insert _ ?diff_value _] =>
    set (diff := diff_value)
  end.
  assert (H_diff : Integer.Valid.t Integer.U128 diff). {
    unfold diff; clear diff.
    pose proof (balance_of_impl_is_valid state from).
    unfold Balance.Valid.t, Integer.Valid.t in *; cbn in *.
    sauto lq: on solve: lia.
  }
  destruct Integer.normalize_with_error as [sum |] eqn:H_sum_eq; cbn; [|easy].
  constructor; cbn.
  destruct state.
  assert (H_sum : Integer.Valid.t Integer.U128 sum). {
    set (balance := erc20.balance_of_impl _ _) in H_sum_eq.
    unfold Integer.normalize_with_error in H_sum_eq.
    unfold Integer.Valid.t; cbn in *.
    repeat destruct (_ <? _) eqn:? in H_sum_eq; try congruence.
    hauto lq: on solve: lia.
  }
  constructor; cbn.
  { repeat (
      apply Mapping.insert_balances_is_valid ||
      assumption ||
      apply H_state
    ).
  }
  { unfold sum_of_money; cbn.
    (* rewrite H_sum_eq; clear H_sum_eq.
    repeat rewrite lib.Mapping.sum_insert.
    pose proof H_storage.(Erc20.Valid.sum _) as H_sum_eq.
    unfold sum_of_money in H_sum_eq; cbn in H_sum_eq; rewrite <- H_sum_eq.
    clear H_sum_eq.
    destruct (AccountId.eq_or_neq to from) as [H_to_from_eq | H_to_from_neq].
    { rewrite H_to_from_eq in *; clear H_to_from_eq.
      unfold erc20.balance_of_impl in *; cbn.
      rewrite lib.Mapping.get_insert_eq; cbn.
      destruct lib.Mapping.get; lia.
    }
    { unfold erc20.balance_of_impl in *; cbn.
      rewrite lib.Mapping.get_insert_neq; [|assumption]; cbn.
      repeat destruct lib.Mapping.get in |- *; lia.
    } *)
    admit.
  }
Admitted.

Lemma transfer_is_valid
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t)
    (H_state : MState.Valid.t state)
    (H_value : Balance.Valid.t value) :
  let '(result, state) :=
    simulations.erc20.transfer env to value state in
  match result with
  | inl _ => MState.Valid.t state
  | _ => True
  end.
Proof.
  now apply transfer_from_to_is_valid.
Qed.

Lemma approve_is_valid
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (spender : erc20.AccountId.t)
    (value : erc20.Balance.t)
    (H_state : MState.Valid.t state)
    (H_value : Balance.Valid.t value) :
  let '(result, state) :=
    simulations.erc20.approve env spender value state in
  MState.Valid.t state.
Proof.
  cbn.
  constructor; try apply H_storage.
  unfold erc20.Env.caller; cbn.
  apply Mapping.insert_allowances_is_valid; sauto lq: on.
Qed.

Lemma transfer_from_is_valid
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t)
    (H_state : MState.Valid.t state)
    (H_value : Balance.Valid.t value) :
  let '(result, state) :=
    simulations.erc20.transfer_from env from to value state in
  match result with
  | inl _ => MState.Valid.t state
  | _ => True
  end.
Proof.
  cbn.
  destruct (_ <? _) eqn:H_lt; [trivial|].
  pose proof (H_transfer :=
    transfer_from_to_is_valid state from to value H_state H_value).
  unfold M.StateError.bind.
  destruct simulations.erc20.transfer_from_to
    as [[?result|?exception] [?storage' ?logs]];
    [|trivial].
  destruct result; cbn; [|trivial].
  constructor; cbn.
  apply Mapping.insert_allowances_is_valid; try apply H_transfer.
  set (allowance := simulations.erc20.allowance_impl _ _ _) in *.
  assert (H_allowance : Balance.Valid.t allowance). {
    apply allowance_impl_is_valid.
    apply H_state.
  }
  unfold Balance.Valid.t, Integer.Valid.t in *; cbn in *.
  lia.
Qed.

Lemma write_dispatch_is_valid
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (write_message : WriteMessage.t)
    (H_state : MState.Valid.t state)
    (H_write_message : WriteMessage.Valid.t write_message) :
  let '(result, state) :=
    WriteMessage.simulation_dispatch env write_message state in
  match result with
  | inl _ => MState.Valid.t state
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
      (state : erc20.MState.t)
      (from : erc20.AccountId.t)
      (to : erc20.AccountId.t)
      (value : erc20.Balance.t) :
    let '(result, state') :=
      simulations.erc20.transfer_from_to from to value state in
    match result with
    | inl _ =>
      state.(erc20.MState.storage).(erc20.Erc20.total_supply) =
      state'.(erc20.MState.storage).(erc20.Erc20.total_supply)
    | _ => True
    end.
  Proof.
    cbn.
    repeat (step; cbn; trivial).
  Qed.

  Lemma transfer_is_constant
      (env : erc20.Env.t)
      (state : erc20.MState.t)
      (to : erc20.AccountId.t)
      (value : erc20.Balance.t) :
    let '(result, state') :=
      simulations.erc20.transfer env to value state in
    match result with
    | inl _ =>
      state.(erc20.MState.storage).(erc20.Erc20.total_supply) =
      state'.(erc20.MState.storage).(erc20.Erc20.total_supply)
    | _ => True
    end.
  Proof.
    apply transfer_from_to_constant.
  Qed.

  Lemma approve_is_constant
      (env : erc20.Env.t)
      (state : erc20.MState.t)
      (spender : erc20.AccountId.t)
      (value : erc20.Balance.t) :
    let '(result, state') :=
      simulations.erc20.approve env spender value state in
    match result with
    | inl _ =>
      state.(erc20.MState.storage).(erc20.Erc20.total_supply) =
      state'.(erc20.MState.storage).(erc20.Erc20.total_supply)
    | _ => True
    end.
  Proof.
    reflexivity.
  Qed.

  Lemma transfer_from_is_constant
      (env : erc20.Env.t)
      (state : erc20.MState.t)
      (from : erc20.AccountId.t)
      (to : erc20.AccountId.t)
      (value : erc20.Balance.t) :
    let '(result, state') :=
      simulations.erc20.transfer_from env from to value state in
    match result with
    | inl _ =>
      state.(erc20.MState.storage).(erc20.Erc20.total_supply) =
      state'.(erc20.MState.storage).(erc20.Erc20.total_supply)
    | _ => True
    end.
  Proof.
    cbn.
    step; cbn; trivial.
    pose proof (transfer_from_to_constant state from to value).
    unfold M.StateError.bind.
    destruct simulations.erc20.transfer_from_to; cbn.
    repeat (step; cbn; trivial).
  Qed.

  Lemma write_dispatch_is_constant
      (env : erc20.Env.t)
      (state : erc20.MState.t)
      (write_message : WriteMessage.t) :
    let '(result, state') :=
      WriteMessage.simulation_dispatch env write_message state in
    match result with
    | inl _ =>
      state.(erc20.MState.storage).(erc20.Erc20.total_supply) =
      state'.(erc20.MState.storage).(erc20.Erc20.total_supply)
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
      (value : erc20.Balance.t) :
      lib.Mapping.t erc20.AccountId.t erc20.Balance.t :=
    if erc20.AccountId.get from =? erc20.AccountId.get to then
      (* Inserting its own value can be useful to initialize an account *)
      simulations.lib.Mapping.insert
        from
        (simulations.erc20.balance_of_impl storage from)
        storage.(erc20.Erc20.balances)
    else
      let from_value := simulations.erc20.balance_of_impl storage from in
      let to_value := simulations.erc20.balance_of_impl storage to in
      simulations.lib.Mapping.insert from (from_value - value)
      (simulations.lib.Mapping.insert to (to_value + value)%Z
      storage.(erc20.Erc20.balances)).

  (** The action on the storage that we can infer from an event. *)
  Definition action_of_event (event : erc20.Event.t) : Action.t :=
    fun storage storage' =>
    match event with
    | erc20.Event.Transfer (erc20.Transfer.Build_t
        (Some from)
        (Some to)
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
          simulations.lib.Mapping.insert (owner, spender) value
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
      (state : erc20.MState.t)
      (from to : erc20.AccountId.t)
      (value : erc20.Balance.t) :
    let storage := state.(erc20.MState.storage) in
    match
      simulations.erc20.transfer_from_to from to value state
    with
    | (inl (inl tt), state') =>
      let storage' := state'.(erc20.MState.storage) in
      storage' =
      storage <|
        erc20.Erc20.balances := balances_of_transfer storage from to value
      |>
    | _ => True
    end.
  Proof.
    cbn.
    destruct (_ <? _) eqn:?; cbn; [easy|].
    unfold Integer.normalize_with_error.
    do 3 (destruct (_ <? _); cbn; [easy|]).
    destruct state; cbn.
    unfold balances_of_transfer.
    destruct (_ =? _) eqn:?.
    { replace to with from in * by sauto l: on.
      set (initial_value := simulations.erc20.balance_of_impl _ _) in *.
      unfold simulations.erc20.balance_of_impl; cbn.
      unfold RecordUpdate.set; f_equal.
      rewrite lib.Mapping.insert_insert by apply AccountId.eq_or_neq.
      f_equal.
      unfold initial_value, simulations.erc20.balance_of_impl; cbn.
      rewrite lib.Mapping.get_insert_eq.
      lia.
    }
    { assert (from <> to) by hauto lq: on solve: lia.
      destruct storage; cbn.
      unfold RecordUpdate.set; f_equal; cbn.
      unfold simulations.erc20.balance_of_impl; cbn.
      rewrite lib.Mapping.get_insert_neq by congruence.
      set (from_value := simulations.lib.Mapping.get from _) in *.
      set (to_value := simulations.lib.Mapping.get to _) in *.
      all: rewrite lib.Mapping.insert_switch;
        try apply AccountId.eq_or_neq;
        try congruence.
    }
  Qed.

  (** The logs of the function [transfer_from_to]. *)
  Lemma event_from_transfer_from_to
      (state : erc20.MState.t)
      (from to : erc20.AccountId.t)
      (value : erc20.Balance.t) :
    match
      simulations.erc20.transfer_from_to from to value state
    with
    | (inl (inl tt), state') =>
      let event := erc20.Event.Transfer {|
        erc20.Transfer.from := Some from;
        erc20.Transfer.to := Some to;
        erc20.Transfer.value := value;
      |} in
      event :: state.(erc20.MState.events) =
      state'.(erc20.MState.events)
    | _ => True
    end.
  Proof.
    cbn.
    destruct (_ <? _); cbn; [easy|].
    now destruct Integer.normalize_with_error.
  Qed.

  (** We show that the action that we infer from the logs is indeed what is
      happening on the storage. *)
  Lemma retrieve_action_from_logs
      (env : erc20.Env.t)
      (storage : erc20.Erc20.t)
      (write_message : WriteMessage.t) :
    let state := erc20.MState.Build_t storage [] in
    match
      WriteMessage.simulation_dispatch env write_message state
    with
    | (inl (inl tt), state') =>
      let storage' := state'.(erc20.MState.storage) in
      let events := state'.(erc20.MState.events) in
      action_of_events events storage storage'
    | _ => True
    end.
  Proof.
    Opaque simulations.erc20.transfer_from_to.
    destruct write_message; cbn;
      unfold simulations.erc20.transfer, M.StateError.bind;
      try (destruct (_ <? _) eqn:?; cbn; [easy|]);
      try match goal with
      | |- context[erc20.transfer_from_to ?from ?to ?value ?state] =>
        pose proof (
          transfer_from_to_on_storage state from to value
        );
        pose proof (
          event_from_transfer_from_to state from to value
        )
      end;
      try destruct simulations.erc20.transfer_from_to
        as [[[[]|?error]|?exception] ?state'];
        sauto.
    Transparent simulations.erc20.transfer_from_to.
  Qed.
End Action_from_log.

(** One can only change its own allowance using the [approve] method. *)
Lemma approve_only_changes_owner_allowance
    (env : erc20.Env.t)
    (state : erc20.MState.t)
    (spender : erc20.AccountId.t)
    (value : erc20.Balance.t) :
  let '(result, state') :=
    simulations.erc20.approve env spender value state in
  match result with
  | inl (inl tt) =>
    forall owner spender,
    let storage := state.(erc20.MState.storage) in
    let storage' := state'.(erc20.MState.storage) in
    simulations.erc20.allowance storage' owner spender <>
      simulations.erc20.allowance storage owner spender ->
    owner = simulations.erc20.Env.caller env
  | _ => True
  end.
Proof.
  unfold erc20.allowance, erc20.allowance_impl; cbn.
  intros.
  match goal with
  | _ : context[
      simulations.lib.Mapping.get ?key1 (simulations.lib.Mapping.insert ?key2 _ _)
    ] |- _ =>
    destruct (AccountId.eq_or_neq_couple key1 key2) as [H_eq | H_neq]
  end.
  { sfirstorder. }
  { rewrite lib.Mapping.get_insert_neq in * by assumption.
    destruct simulations.lib.Mapping.get; lia.
  }
Qed.
