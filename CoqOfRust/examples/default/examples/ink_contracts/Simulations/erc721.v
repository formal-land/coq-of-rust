Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.Simulations.M.
Require CoqOfRust.examples.default.examples.ink_contracts.erc721.

Import Simulations.M.Notations.

(** ** Primitives *)

Module Env.
  Definition caller (self : erc721.Env.t) : erc721.AccountId.t :=
    self.(erc721.Env.caller).

  Definition emit_event
      (events : list erc721.Event.t)
      (event : erc721.Event.t) :
      list erc721.Event.t :=
    event :: events.
End Env.

Definition env (env : erc721.Env.t) : erc721.Env.t :=
  env.

Module AccountId.
  Definition eq (x y : erc721.AccountId.t) : bool.t :=
    BinOp.Pure.eq (erc721.AccountId.x0 x) (erc721.AccountId.x0 y).

  Definition neq (x y : erc721.AccountId.t) : bool.t :=
    negb (eq x y).

  Definition option_eq (x y : core.option.Option.t erc721.AccountId.t) : bool.t :=
    match x, y with
    | core.option.Option.Some x, core.option.Option.Some y => eq x y
    | core.option.Option.None, core.option.Option.None => true
    | _, _ => false
    end.

  Definition option_neq (x y : core.option.Option.t erc721.AccountId.t) : bool.t :=
    negb (option_eq x y).

  Parameter from : array u8.t -> erc721.AccountId.t.
End AccountId.

(** ** Simulations that only read the state. *)

Definition balance_of_or_zero
    (storage : erc721.Erc721.t)
    (owner : erc721.AccountId.t) :
    u32.t :=
  match Lib.Mapping.get owner storage.(erc721.Erc721.owned_tokens_count) with
  | option.Option.Some count => count
  | option.Option.None => u32.Make 0
  end.

Definition approved_for_all
    (storage : erc721.Erc721.t)
    (owner : erc721.AccountId.t)
    (operator : erc721.AccountId.t) :
    bool.t :=
  Lib.Mapping.contains (owner, operator) storage.(erc721.Erc721.operator_approvals).

Definition owner_of
    (storage : erc721.Erc721.t)
    (token_id : ltac:(erc721.TokenId)) :
    core.option.Option.t erc721.AccountId.t :=
  Lib.Mapping.get token_id storage.(erc721.Erc721.token_owner).

Definition approved_or_owner
    (storage : erc721.Erc721.t)
    (from : core.option.Option.t erc721.AccountId.t)
    (token_id : ltac:(erc721.TokenId)) :
    bool.t :=
  let owner := owner_of storage token_id in
  (AccountId.option_neq
    from
    (option.Option.Some (AccountId.from (repeat (u8.Make 0) 32)))
  && (AccountId.option_eq from owner
    || AccountId.option_eq
        from
        (Lib.Mapping.get token_id storage.(erc721.Erc721.token_approvals))
    (* || approved_for_all storage owner from *)
    ))%bool.

Definition exists_
    (storage : erc721.Erc721.t)
    (token_id : ltac:(erc721.TokenId)) :
    bool.t :=
  Lib.Mapping.contains token_id storage.(erc721.Erc721.token_owner).

Definition balance_of
    (storage : erc721.Erc721.t)
    (owner : erc721.AccountId.t) :
    u32.t :=
  balance_of_or_zero storage owner.

Definition get_approved 
    (storage : erc721.Erc721.t)
    (token_id : ltac:(erc721.TokenId)) :
    core.option.Option.t erc721.AccountId.t :=
  Lib.Mapping.get token_id storage.(erc721.Erc721.token_approvals).

Definition is_approved_for_all
    (storage : erc721.Erc721.t)
    (owner : erc721.AccountId.t)
    (operator : erc721.AccountId.t) :
    bool.t :=
  approved_for_all storage owner operator.

(** ** Simulations modifying the state. *)

Module State.
  Definition t : Set := erc721.Erc721.t * list erc721.Event.t.
End State.

Definition clear_approval
    (token_id : ltac:(erc721.TokenId)) :
    MS? State.t unit :=
  letS? '(storage, events) := readS? in
  let storage' :=
    storage <|
      erc721.Erc721.token_approvals :=
        Lib.Mapping.remove token_id storage.(erc721.Erc721.token_approvals)
    |> in
  letS? _ := writeS? (storage', events) in
  returnS? tt.

Definition approve_for_all
    (env : erc721.Env.t)
    (to : erc721.AccountId.t)
    (approved : bool.t) :
    MS? State.t (core.result.Result.t unit erc721.Error.t) :=
  let caller := Env.caller env in
  if AccountId.eq to caller
  then
    letS? '(storage, events) := readS? in
    let event := erc721.Event.ApprovalForAll {|
      erc721.ApprovalForAll.owner := caller;
      erc721.ApprovalForAll.operator := to;
      erc721.ApprovalForAll.approved := approved
    |} in
    letS? _ := writeS? (
      storage <| erc721.Erc721.operator_approvals :=
        if approved
        then
          Lib.Mapping.insert (caller, to) tt storage.(erc721.Erc721.operator_approvals)
        else
          Lib.Mapping.remove (caller, to) storage.(erc721.Erc721.operator_approvals)
      |>,
      event :: events
    ) in
    returnS? (result.Result.Ok tt)
  else
    returnS? (result.Result.Err erc721.Error.NotApproved). 

Definition set_approval_for_all
    (env : erc721.Env.t)
    (to : erc721.AccountId.t)
    (approved : bool.t) :
    MS? State.t (core.result.Result.t unit erc721.Error.t) :=
  approve_for_all env to approved.

(* TODO: *)
(* approve_for *)
(* approve *)
(* remove_token_from *)
(* add_token_to *)
(* transfer_token_from *)
(* transfer *)
(* transfer_from *)
(* mint *)
(* burn *)