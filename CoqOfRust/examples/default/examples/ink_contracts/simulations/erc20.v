Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.simulations.M.
Require CoqOfRust.examples.default.examples.ink_contracts.erc20.

Import simulations.M.Notations.

(** ** Primitives *)

Module Option.
  Definition to_value {A : Set} (x : option A) (f : A -> Value.t) : Value.t :=
    match x with
    | None => Value.StructTuple "core::option::Option::None" []
    | Some x => Value.StructTuple "core::option::Option::Some" [f x]
    end.
End Option.

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
      ("from", Option.to_value x.(from) AccountId.to_value);
      ("to", Option.to_value x.(to) AccountId.to_value);
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

Definition env (env : erc20.Env.t) : erc20.Env.t :=
  env.

Module Erc20.
  Record t : Set := {
    total_supply : Balance.t;
    balances : Lib.Mapping.t AccountId.t Balance.t;
    allowances : Lib.Mapping.t (AccountId.t * AccountId.t) Balance.t;
  }.

  Definition to_value (x : t) : Value.t :=
    Value.StructRecord "erc20::Erc20" [
      ("total_supply", Balance.to_value x.(total_supply));
      ("balances", Lib.Mapping.to_value AccountId.to_value Balance.to_value x.(balances));
      ("allowances", Lib.Mapping.to_value (AccountId.to_value * AccountId.to_value) Balance.to_value x.(allowances))
    ].
End Erc20.

(** ** Simulations that only read the state. *)

Definition total_supply (storage : erc20.Erc20.t) : erc20.Balance.t :=
  storage.(erc20.Erc20.total_supply).

Definition balance_of_impl
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t) :
    ltac:(erc20.Balance) :=
  match Lib.Mapping.get owner storage.(erc20.Erc20.balances) with
  | option.Option.Some balance => balance
  | option.Option.None => u128.Make 0
  end.

Definition balance_of
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t) :
    ltac:(erc20.Balance) :=
  balance_of_impl storage owner.

Definition allowance_impl
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t)
    (spender : erc20.AccountId.t) :
    ltac:(erc20.Balance) :=
  match Lib.Mapping.get (owner, spender) storage.(erc20.Erc20.allowances) with
  | option.Option.Some allowance => allowance
  | option.Option.None => u128.Make 0
  end.

Definition allowance
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t)
    (spender : erc20.AccountId.t) :
    ltac:(erc20.Balance) :=
  allowance_impl storage owner spender.

(** ** Simulations modifying the state. *)

Module State.
  Definition t : Set := erc20.Erc20.t * list erc20.Event.t.
End State.

Definition transfer_from_to
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
    MS? State.t ltac:(erc20.Result unit) :=
  letS? '(storage, events) := readS? in
  let from_balance := balance_of_impl storage from in
  if from_balance <u128 value then
    returnS? (result.Result.Err erc20.Error.InsufficientBalance)
  else
    let new_from_balance := BinOp.Optimistic.sub from_balance value in
    letS? _ := writeS? (
      storage <| erc20.Erc20.balances :=
        Lib.Mapping.insert from new_from_balance
          storage.(erc20.Erc20.balances)
      |>,
      events
    ) in
    letS? '(storage, events) := readS? in
    let to_balance := balance_of_impl storage to in
    letS? new_to_balance := return?toS? (BinOp.Error.add to_balance value) in
    let event := erc20.Event.Transfer {|
      erc20.Transfer.from := option.Option.Some from;
      erc20.Transfer.to := option.Option.Some to;
      erc20.Transfer.value := value
    |} in
    letS? _ := writeS? (
      storage <| erc20.Erc20.balances :=
        Lib.Mapping.insert to new_to_balance
          storage.(erc20.Erc20.balances)
      |>,
      event :: events
    ) in
    returnS? (result.Result.Ok tt).

Definition transfer
    (env : erc20.Env.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
    MS? State.t ltac:(erc20.Result unit) :=
  transfer_from_to (Env.caller env) to value.

Definition approve
    (env : erc20.Env.t)
    (spender : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
    MS? State.t ltac:(erc20.Result unit) :=
  let owner := Env.caller env in
  letS? '(storage, events) := readS? in
  let event := erc20.Event.Approval {|
    erc20.Approval.owner := (erc20.env env).(ink_contracts.erc20.Env.caller);
    erc20.Approval.spender := spender;
    erc20.Approval.value := value
  |} in
  letS? _ := writeS? (
    storage <| erc20.Erc20.allowances :=
      Lib.Mapping.insert (owner, spender) value
        storage.(erc20.Erc20.allowances)
    |>,
    event :: events
  ) in
  returnS? (result.Result.Ok tt).

Definition transfer_from
    (env : erc20.Env.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
    MS? State.t ltac:(erc20.Result unit) :=
  let caller := Env.caller env in
  letS? '(storage, events) := readS? in
  let allowance := allowance_impl storage from caller in
  if allowance <u128 value then
    returnS? (result.Result.Err erc20.Error.InsufficientAllowance)
  else
    letS? result_from_to := transfer_from_to from to value in
    match result_from_to with
    | result.Result.Err _ => returnS? (result_from_to)
    | result.Result.Ok _ =>
      let new_allowance := BinOp.Optimistic.sub allowance value in
      letS? '(storage, events) := readS? in
      letS? _ := writeS? (
        storage <| erc20.Erc20.allowances :=
          Lib.Mapping.insert (from, caller) new_allowance
            storage.(erc20.Erc20.allowances)
        |>,
        events
      ) in
      returnS? (result.Result.Ok tt)
    end.
