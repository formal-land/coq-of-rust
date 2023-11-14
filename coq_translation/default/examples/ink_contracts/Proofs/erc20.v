Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.Proofs.M.
Require CoqOfRust.examples.ink_contracts.erc20.

Module State.
  Module State.
    (** The state is a single cell containing the contract's state. This is an
        option type as it may or may not be allocated. *)
    Definition t : Set := option erc20.Erc20.t.
  End State.

  Module Address.
    (** As there is a single cell in the state, the address type carries no
        information. *)
    Definition t : Set := unit.
  End Address.

  Global Instance I : State.Trait State.t Address.t := {
    State.get_Set address :=
      match address with
      | tt => erc20.Erc20.t
      end;
    State.read address state :=
      match address with
      | tt => state
      end;
    State.alloc_write address state value :=
      match address, value with
      | tt, _ => Some (Some value)
      end;
  }.

  Lemma is_valid : State.Valid.t I.
  Proof.
    sauto lq: on rew: off.
  Qed.
End State.

Ltac run_symbolic_state_read :=
  match goal with
  | |- Run.t (LowM.CallPrimitive (Primitive.StateRead ?address)) _ _ _ =>
    let H := fresh "H" in
    pose proof (H := Run.CallPrimitiveStateRead address);
    apply H; reflexivity;
    clear H
  end.

Ltac run_symbolic_one_step :=
  match goal with
  | |- Run.t _ _ _ _ =>
    econstructor ||
    run_symbolic_state_read
  end.

Ltac run_symbolic :=
  repeat run_symbolic_one_step.

(** Starting from a state with a given [balance] for a given [owner], when we
    read that information we get the expected [balance]. *)
Lemma run_balance_of_impl
  (owner : erc20.AccountId.t)
  (balance : Z)
  fuel :
  (* An initial state *)
  let state := Some ({|
    erc20.Erc20.total_supply := 0;
    erc20.Erc20.balances := Lib.Mapping.insert owner balance Lib.Mapping.empty;
    erc20.Erc20.allowances := Lib.Mapping.empty;
  |}) in
  (* The value [self] is allocated in the state *)
  let self : M.Val (ref erc20.Erc20.t) := Ref.Imm (Ref.mut_ref tt) in
  (* The value [owner] is an immediate value *)
  let owner : M.Val (ref erc20.AccountId.t) := Ref.Imm (Ref.Imm owner) in
  Run.t
    (erc20.Impl_erc20_Erc20_t_2.balance_of_impl self owner fuel)
    state
    (* expected output *)
    (inl (Ref.Imm balance))
    (* the state does not change *)
    state.
Proof.
  unfold erc20.Impl_erc20_Erc20_t_2.balance_of_impl.
  run_symbolic.
  { simpl.
    rewrite Lib.Mapping.get_insert_eq.
    run_symbolic.
  }
  { run_symbolic. }
Qed.
