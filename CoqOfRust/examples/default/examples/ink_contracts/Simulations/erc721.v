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

(* TODO *)

(** ** Simulations modifying the state. *)

(* TODO *)