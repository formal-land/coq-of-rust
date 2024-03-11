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
    bool.t.
  (* let owner := owner_of storage token_id in *)
Admitted.

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

(* TODO: *)
(* clear_approval *)
(* approve_for_all *)
(* set_approval_for_all *)
(* approve_for *)
(* approve *)
(* remove_token_from *)
(* add_token_to *)
(* transfer_token_from *)
(* transfer *)
(* transfer_from *)
(* mint *)
(* burn *)