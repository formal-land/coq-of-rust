Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.examples.default.examples.ink_contracts.erc20.

(** ** Simulations that only read the state. *)

Definition total_supply (storage : erc20.Erc20.t) : ltac:(erc20.Balance) :=
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

Definition transfer_from_to
    (storage : erc20.Erc20.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
    M? (ltac:(erc20.Result unit) * erc20.Erc20.t) :=
  let from_balance := balance_of_impl storage from in
  if from_balance <u128 value then
    return? (result.Result.Err erc20.Error.InsufficientBalance, storage)
  else
    let new_from_balance := BinOp.Optimistic.sub from_balance value in
    let storage := storage <| erc20.Erc20.balances :=
      Lib.Mapping.insert from new_from_balance
        storage.(erc20.Erc20.balances)
    |> in
    let to_balance := balance_of_impl storage to in
    let? new_to_balance := BinOp.Option.add to_balance value in
    let storage := storage <| erc20.Erc20.balances :=
      Lib.Mapping.insert to new_to_balance
        storage.(erc20.Erc20.balances)
    |> in
    return? (result.Result.Ok tt, storage).

Definition transfer
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
    M? (ltac:(erc20.Result unit) * erc20.Erc20.t) :=
  transfer_from_to storage env.(erc20.Env.caller) to value.

Definition approve
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (spender : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
    ltac:(erc20.Result unit) * erc20.Erc20.t :=
  let owner := env.(erc20.Env.caller) in
  let storage := storage <| erc20.Erc20.allowances :=
    Lib.Mapping.insert (owner, spender) value storage.(erc20.Erc20.allowances)
  |> in
  (result.Result.Ok tt, storage).

Definition transfer_from
    (env : erc20.Env.t)
    (storage : erc20.Erc20.t)
    (from : erc20.AccountId.t)
    (to : erc20.AccountId.t)
    (value : ltac:(erc20.Balance)) :
    M? (ltac:(erc20.Result unit) * erc20.Erc20.t) :=
  let caller := env.(erc20.Env.caller) in
  let allowance := allowance_impl storage from caller in
  if allowance <u128 value then
    return? (result.Result.Err erc20.Error.InsufficientAllowance, storage)
  else
    let? '(result_from_to, storage) := transfer_from_to storage from to value in
    match result_from_to with
    | result.Result.Err _ => return? (result_from_to, storage)
    | result.Result.Ok _ =>
      let new_allowance := BinOp.Optimistic.sub allowance value in
      let storage := storage <| erc20.Erc20.allowances :=
        Lib.Mapping.insert (from, caller) new_allowance
          storage.(erc20.Erc20.allowances)
      |> in
      return? (result.Result.Ok tt, storage)
    end.
