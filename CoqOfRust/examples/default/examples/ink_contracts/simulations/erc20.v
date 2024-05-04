Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.core.simulations.default.
Require CoqOfRust.core.simulations.option.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.lib.
Require Import CoqOfRust.lib.simulations.lib.
Require Import CoqOfRust.simulations.M.

Import simulations.M.Notations.

(** ** Primitives *)

Module Balance.
  Definition t : Set := u128.t.
End Balance.

Module Impl_Default_for_Balance.
  Global Instance I : core.simulations.default.Default.Trait Balance.t := {
    default := u128.Make 0;
  }.
End Impl_Default_for_Balance.

Module AccountId.
  Inductive t : Set :=
  | Make (account_id : u128.t).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc20::AccountId";
    φ '(Make x) := Value.StructTuple "erc20::AccountId" [φ x];
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
      | Transfer x => Value.StructTuple "erc20::Event::Transfer" [φ x]
      | Approval x => Value.StructTuple "erc20::Event::Approval" [φ x]
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
      | InsufficientBalance => Value.StructTuple "erc20::Error::InsufficientBalance" []
      | InsufficientAllowance => Value.StructTuple "erc20::Error::InsufficientAllowance" []
      end;
  }.
End Error.

Module Result.
  Definition t (A : Set) : Set := A + Error.t.
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

  Module SubPointer.
    Definition get_total_supply : SubPointer.Runner.t t Balance.t := {|
      SubPointer.Runner.index := Pointer.Index.StructRecord "erc20::Erc20" "total_supply";
      SubPointer.Runner.projection x := Some x.(total_supply);
      SubPointer.Runner.injection x y := Some (x <| total_supply := y |>);
    |}.

    Definition get_balances :
        SubPointer.Runner.t t (simulations.lib.Mapping.t AccountId.t Balance.t) := {|
      SubPointer.Runner.index := Pointer.Index.StructRecord "erc20::Erc20" "balances";
      SubPointer.Runner.projection x := Some x.(balances);
      SubPointer.Runner.injection x y := Some (x <| balances := y |>);
    |}.

    Definition get_allowances : SubPointer.Runner.t t
        (simulations.lib.Mapping.t (AccountId.t * AccountId.t) Balance.t) := {|
      SubPointer.Runner.index := Pointer.Index.StructRecord "erc20::Erc20" "allowances";
      SubPointer.Runner.projection x := Some x.(allowances);
      SubPointer.Runner.injection x y := Some (x <| allowances := y |>);
    |}.
  End SubPointer.
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
  | None => u128.Make 0
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
  | None => u128.Make 0
  end.

Definition allowance
    (storage : erc20.Erc20.t)
    (owner : erc20.AccountId.t)
    (spender : erc20.AccountId.t) :
    erc20.Balance.t :=
  allowance_impl storage owner spender.

(** ** Simulations modifying the state. *)

Module MState.
  Record t : Set := {
    storage : erc20.Erc20.t;
    events : list erc20.Event.t;
  }.
End MState.

Definition transfer_from_to
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t) :
    MS? MState.t string (erc20.Result.t unit) :=
  letS? '{| MState.storage := storage; MState.events := events |} := readS? in
  let from_balance := u128.get (balance_of_impl storage from) in
  if from_balance <? u128.get value then
    returnS? (inr erc20.Error.InsufficientBalance)
  else
    let new_from_balance := u128.Make (from_balance - u128.get value) in
    letS? _ := writeS? {|
      MState.storage := storage <| erc20.Erc20.balances :=
        simulations.lib.Mapping.insert from new_from_balance
          storage.(erc20.Erc20.balances)
      |>;
      MState.events := events;
    |} in
    letS? '{| MState.storage := storage; MState.events := events |} := readS? in
    let 'u128.Make to_balance := balance_of_impl storage to in
    letS? new_to_balance :=
      return?toS? (
        Integer.normalize_with_error Integer.U128 (to_balance + u128.get value)
      ) in
    let event := erc20.Event.Transfer {|
      erc20.Transfer.from := Some from;
      erc20.Transfer.to := Some to;
      erc20.Transfer.value := value
    |} in
    letS? _ := writeS? {|
      MState.storage := storage <| erc20.Erc20.balances :=
        simulations.lib.Mapping.insert to (u128.Make new_to_balance)
          storage.(erc20.Erc20.balances)
      |>;
      MState.events := event :: events;
    |} in
    returnS? (inl tt).

Definition transfer
    (env : erc20.Env.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t) :
    MS? MState.t string (erc20.Result.t unit) :=
  transfer_from_to (Env.caller env) to value.

Definition approve
    (env : erc20.Env.t)
    (spender : erc20.AccountId.t)
    (value : erc20.Balance.t) :
    MS? MState.t string (erc20.Result.t unit) :=
  let owner := Env.caller env in
  letS? '{| MState.storage := storage; MState.events := events |} := readS? in
  let event := erc20.Event.Approval {|
    erc20.Approval.owner := (erc20.env env).(erc20.Env.caller);
    erc20.Approval.spender := spender;
    erc20.Approval.value := value
  |} in
  letS? _ := writeS? {|
    MState.storage :=  storage <| erc20.Erc20.allowances :=
      simulations.lib.Mapping.insert (owner, spender) value
        storage.(erc20.Erc20.allowances)
    |>;
    MState.events := event :: events;
  |} in
  returnS? (inl tt).

Definition transfer_from
    (env : erc20.Env.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : erc20.Balance.t) :
    MS? MState.t string (erc20.Result.t unit) :=
  let caller := Env.caller env in
  letS? '{| MState.storage := storage; MState.events := events |} := readS? in
  let 'u128.Make value := value in
  let 'u128.Make allowance := allowance_impl storage from caller in
  if allowance <? value then
    returnS? (inr erc20.Error.InsufficientAllowance)
  else
    letS? result_from_to := transfer_from_to from to (u128.Make value) in
    match result_from_to with
    | inr _ => returnS? result_from_to
    | inl _ =>
      let new_allowance := u128.Make (allowance - value) in
      letS? '{| MState.storage := storage; MState.events := events |} := readS? in
      letS? _ := writeS? {|
        MState.storage := storage <| erc20.Erc20.allowances :=
          simulations.lib.Mapping.insert (from, caller) new_allowance
            storage.(erc20.Erc20.allowances)
        |>;
        MState.events := events;
      |} in
      returnS? (inl tt)
    end.
