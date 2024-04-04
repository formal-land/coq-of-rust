Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.examples.default.examples.ink_contracts.erc20.
Require CoqOfRust.core.simulations.default.
Require CoqOfRust.core.simulations.option.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.lib.
Require Import CoqOfRust.simulations.M.

Import simulations.M.Notations.

(** ** Primitives *)

Module Balance.
  Inductive t : Set :=
  | Make (balance : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc20::Balance";
    φ '(Make x) := Value.Integer Integer.U128 x;
  }.
End Balance.

Module Impl_Default_for_Balance.
  Global Instance I : core.simulations.default.Default.Trait Balance.t := {
    default := Balance.Make 0;
  }.
End Impl_Default_for_Balance.

Module AccountId.
  Inductive t : Set :=
  | Make (account_id : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc20::AccountId";
    φ '(Make x) :=
      Value.StructTuple "erc20::AccountId" [Value.Integer Integer.U128 x];
  }.
End AccountId.

Module Transfer.
  Record t : Set := {
    from : option AccountId.t;
    to : option AccountId.t;
    value : Balance.t;
  }.

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc20::Transfer";
    φ x :=
      Value.StructRecord "erc20::Transfer" [
        ("from", φ x.(from));
        ("to", φ x.(to));
        ("value", φ x.(value))
      ];
  }.
End Transfer.

Module Approval.
  Record t : Set := {
    owner : AccountId.t;
    spender : AccountId.t;
    value : Balance.t;
  }.

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc20::Approval";
    φ x :=
      Value.StructRecord "erc20::Approval" [
        ("owner", φ x.(owner));
        ("spender", φ x.(spender));
        ("value", φ x.(value))
      ];
  }.
End Approval.

Module Event.
  Inductive t : Set :=
  | Transfer : erc20.Transfer.t -> t
  | Approval : erc20.Approval.t -> t.

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc20::Event";
    φ x :=
      match x with
      | Transfer x => φ x
      | Approval x => φ x
      end;
  }.
End Event.

Module Env.
  Record t : Set := {
    caller : AccountId.t;
  }.

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc20::Env";
    φ x :=
      Value.StructRecord "erc20::Env" [
        ("caller", φ x.(caller))
      ];
  }.

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

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc20::Error";
    φ x :=
      match x with
      | InsufficientBalance => Value.StructTuple "erc20::Error" []
      | InsufficientAllowance => Value.StructTuple "erc20::Error" []
      end;
  }.
End Error.

Module Result.
  Definition t (A : Set) : Set := A + Error.t.

  Global Instance IsToValue (A : Set) (_ : ToValue A) : ToValue (t A) := {
    Φ := Ty.path "erc20::Result";
    φ x :=
      match x with
      | inl ok => Value.StructTuple "erc20::Result::OK" [φ ok]
      | inr err => φ err
      end;
  }.
End Result.

Definition init_env (env : erc20.Env.t) : erc20.Env.t :=
  env.

Definition env (env : erc20.Env.t) : erc20.Env.t :=
  env.

Module Erc20.
  Record t : Set := {
    total_supply : Balance.t;
    balances : simulations.lib.Mapping.t AccountId.t Balance.t;
    allowances :
      simulations.lib.Mapping.t (AccountId.t * AccountId.t) Balance.t;
  }.

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc20::Erc20";
    φ x :=
      Value.StructRecord "erc20::Erc20" [
        ("total_supply", φ x.(total_supply));
        ("balances", φ x.(balances));
        ("allowances", φ x.(allowances))
      ];
  }.
End Erc20.

(** ** Simulations that only read the state. *)

Definition total_supply (storage : erc20.Erc20.t) : erc20.Balance.t :=
  storage.(erc20.Erc20.total_supply).

Definition balance_of_impl
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t) :
    erc20.Balance.t :=
  match simulations.lib.Mapping.get owner storage.(erc20.Erc20.balances) with
  | Some balance => balance
  | None => Balance.Make 0
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
      (owner, spender)
      storage.(erc20.Erc20.allowances)
  with
  | Some allowance => allowance
  | None => Balance.Make 0
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
    MS? State.t string (erc20.Result.t unit) :=
  letS? '(storage, events) := readS? in
  let 'Balance.Make value := value in
  let 'Balance.Make from_balance := balance_of_impl storage from in
  if from_balance <? value then
    returnS? (inr erc20.Error.InsufficientBalance)
  else
    let new_from_balance := Balance.Make (from_balance - value) in
    letS? _ := writeS? (
      storage <| erc20.Erc20.balances :=
        simulations.lib.Mapping.insert from new_from_balance
          storage.(erc20.Erc20.balances)
      |>,
      events
    ) in
    letS? '(storage, events) := readS? in
    let 'Balance.Make to_balance := balance_of_impl storage to in
    letS? new_to_balance :=
      return?toS? (
        Integer.normalize_with_error Integer.U128 (to_balance + value)
      ) in
    let event := erc20.Event.Transfer {|
      erc20.Transfer.from := Some from;
      erc20.Transfer.to := Some to;
      erc20.Transfer.value := Balance.Make value
    |} in
    letS? _ := writeS? (
      storage <| erc20.Erc20.balances :=
        simulations.lib.Mapping.insert to (Balance.Make new_to_balance)
          storage.(erc20.Erc20.balances)
      |>,
      event :: events
    ) in
    returnS? (inl tt).

Definition transfer
    (env : erc20.Env.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t) :
    MS? State.t string (erc20.Result.t unit) :=
  transfer_from_to (Env.caller env) to value.

Definition approve
    (env : erc20.Env.t)
    (spender : erc20.AccountId.t)
    (value : erc20.Balance.t) :
    MS? State.t string (erc20.Result.t unit) :=
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
    MS? State.t string (erc20.Result.t unit) :=
  let caller := Env.caller env in
  letS? '(storage, events) := readS? in
  let 'Balance.Make value := value in
  let 'Balance.Make allowance := allowance_impl storage from caller in
  if allowance <? value then
    returnS? (inr erc20.Error.InsufficientAllowance)
  else
    letS? result_from_to := transfer_from_to from to (Balance.Make value) in
    match result_from_to with
    | inr _ => returnS? (result_from_to)
    | inl _ =>
      let new_allowance := Balance.Make (allowance - value) in
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
