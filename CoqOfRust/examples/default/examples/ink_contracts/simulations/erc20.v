Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.examples.default.examples.ink_contracts.erc20.

Require CoqOfRust.core.simulations.option.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.lib.
Require CoqOfRust.simulations.M.

Import simulations.M.Notations.

(** ** Primitives *)

Module Balance.
  Definition t : Set := Z.

  Definition to_value (x : t) : Value.t :=
    Value.Integer Integer.U128 x.
End Balance.

Module AccountId.
  Definition t : Set := Z.

  Definition to_value (x : t) : Value.t :=
    Value.StructTuple "erc20::AccountId" [Value.Integer Integer.U128 x].
End AccountId.

Module Transfer.
  Record t : Set := {
    from : option AccountId.t;
    to : option AccountId.t;
    value : Balance.t;
  }.

  Definition to_value (x : t) : Value.t :=
    Value.StructRecord "erc20::Transfer" [
      ("from",
        core.simulations.option.Option.to_value x.(from) AccountId.to_value);
      ("to",
        core.simulations.option.Option.to_value x.(to) AccountId.to_value);
      ("value", Balance.to_value x.(value))
    ].
End Transfer.

Module Approval.
  Record t : Set := {
    owner : AccountId.t;
    spender : AccountId.t;
    value : Balance.t;
  }.

  Definition to_value (x : t) : Value.t :=
    Value.StructRecord "erc20::Approval" [
      ("owner", AccountId.to_value x.(owner));
      ("spender", AccountId.to_value x.(spender));
      ("value", Balance.to_value x.(value))
    ].
End Approval.

Module Event.
  Inductive t : Set :=
  | Transfer : erc20.Transfer.t -> t
  | Approval : erc20.Approval.t -> t.

  Definition to_value (x : t) : Value.t :=
    match x with
    | Transfer x => Transfer.to_value x
    | Approval x => Approval.to_value x
    end.
End Event.

Module Env.
  Record t : Set := {
    caller : AccountId.t;
  }.

  Definition to_value (x : t) : Value.t :=
    Value.StructRecord "erc20::Env" [
      ("caller", AccountId.to_value x.(caller))
    ].

  Definition emit_event
      (events : list erc20.Event.t)
      (event : erc20.Event.t) :
      list erc20.Event.t :=
    event :: events.
End Env.

Module Error.
  Inductive t : Set :=
  | InsufficientBalance
  | InsufficientAllowance.

  Definition to_value (x : t) : Value.t :=
    match x with
    | InsufficientBalance => Value.StructTuple "erc20::Error" []
    | InsufficientAllowance => Value.StructTuple "erc20::Error" []
    end.
End Error.

Module Result.
  Definition t (A : Set) : Set := A + Error.t.

  Definition to_value {A : Set} (A_to_value : A -> Value.t) (x : t A) :
      Value.t :=
    match x with
    | inl ok => Value.StructTuple "core::result::Result::OK" [A_to_value ok]
    | inr err => Value.StructTuple "core::result::Result" [Error.to_value err]
    end.
End Result.

Definition env (env : erc20.Env.t) : erc20.Env.t :=
  env.

Module Erc20.
  Record t : Set := {
    total_supply : Balance.t;
    balances : simulations.lib.Mapping.t AccountId.t Balance.t;
    allowances :
      simulations.lib.Mapping.t (AccountId.t * AccountId.t) Balance.t;
  }.

  Definition to_value (x : t) : Value.t :=
    Value.StructRecord "erc20::Erc20" [
      ("total_supply", Balance.to_value x.(total_supply));
      ("balances",
        simulations.lib.Mapping.to_value
          AccountId.to_value
          Balance.to_value
          x.(balances));
      ("allowances",
        simulations.lib.Mapping.to_value
          (fun '(owner, spender) =>
            Value.Tuple [AccountId.to_value owner; AccountId.to_value spender])
          Balance.to_value
          x.(allowances))
    ].
End Erc20.

(** ** Simulations that only read the state. *)

Definition total_supply (storage : erc20.Erc20.t) : erc20.Balance.t :=
  storage.(erc20.Erc20.total_supply).

Definition balance_of_impl
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t) :
    erc20.Balance.t :=
  match simulations.lib.Mapping.get storage.(erc20.Erc20.balances) owner with
  | Some balance => balance
  | None => 0
  end.

Definition balance_of
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t) :
    erc20.Balance.t :=
  balance_of_impl storage owner.

Definition allowance_impl
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t)
    (spender : erc20.AccountId.t) :
    erc20.Balance.t :=
  match
    simulations.lib.Mapping.get
      storage.(erc20.Erc20.allowances)
      (owner, spender)
  with
  | Some allowance => allowance
  | None => 0
  end.

Definition allowance
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t)
    (spender : erc20.AccountId.t) :
    erc20.Balance.t :=
  allowance_impl storage owner spender.

(** ** Simulations modifying the state. *)

Module State.
  Definition t : Set := erc20.Erc20.t * list erc20.Event.t.
End State.

Definition transfer_from_to
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t) :
    MS? State.t (erc20.Result.t unit) :=
  letS? '(storage, events) := readS? in
  let from_balance := balance_of_impl storage from in
  if from_balance <? value then
    returnS? (inr erc20.Error.InsufficientBalance)
  else
    let new_from_balance := from_balance - value in
    letS? _ := writeS? (
      storage <| erc20.Erc20.balances :=
        simulations.lib.Mapping.insert from new_from_balance
          storage.(erc20.Erc20.balances)
      |>,
      events
    ) in
    letS? '(storage, events) := readS? in
    let to_balance := balance_of_impl storage to in
    letS? new_to_balance :=
      return?toS?
        (Integer.normalize_with_error Integer.U128 (to_balance + value)) in
    let event := erc20.Event.Transfer {|
      erc20.Transfer.from := Some from;
      erc20.Transfer.to := Some to;
      erc20.Transfer.value := value
    |} in
    letS? _ := writeS? (
      storage <| erc20.Erc20.balances :=
        simulations.lib.Mapping.insert to new_to_balance
          storage.(erc20.Erc20.balances)
      |>,
      event :: events
    ) in
    returnS? (inl tt).

Definition transfer
    (env : erc20.Env.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t) :
    MS? State.t (erc20.Result.t unit) :=
  transfer_from_to (Env.caller env) to value.

Definition approve
    (env : erc20.Env.t)
    (spender : erc20.AccountId.t)
    (value : erc20.Balance.t) :
    MS? State.t (erc20.Result.t unit) :=
  let owner := Env.caller env in
  letS? '(storage, events) := readS? in
  let event := erc20.Event.Approval {|
    erc20.Approval.owner := (erc20.env env).(erc20.Env.caller);
    erc20.Approval.spender := spender;
    erc20.Approval.value := value
  |} in
  letS? _ := writeS? (
    storage <| erc20.Erc20.allowances :=
      simulations.lib.Mapping.insert (owner, spender) value
        storage.(erc20.Erc20.allowances)
    |>,
    event :: events
  ) in
  returnS? (inl tt).

Definition transfer_from
    (env : erc20.Env.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t) :
    MS? State.t (erc20.Result.t unit) :=
  let caller := Env.caller env in
  letS? '(storage, events) := readS? in
  let allowance := allowance_impl storage from caller in
  if allowance <? value then
    returnS? (inr erc20.Error.InsufficientAllowance)
  else
    letS? result_from_to := transfer_from_to from to value in
    match result_from_to with
    | inr _ => returnS? (result_from_to)
    | inl _ =>
      let new_allowance := allowance - value in
      letS? '(storage, events) := readS? in
      letS? _ := writeS? (
        storage <| erc20.Erc20.allowances :=
          simulations.lib.Mapping.insert (from, caller) new_allowance
            storage.(erc20.Erc20.allowances)
        |>,
        events
      ) in
      returnS? (inl tt)
    end.
