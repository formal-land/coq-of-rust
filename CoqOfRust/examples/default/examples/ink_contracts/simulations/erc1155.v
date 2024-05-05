Require Import CoqOfRust.CoqOfRust.
Require CoqOfRust.core.simulations.default.
Require Import CoqOfRust.core.simulations.option.
Require Import CoqOfRust.core.simulations.integer.
Require Import CoqOfRust.core.simulations.bool.
Require CoqOfRust.examples.default.examples.ink_contracts.simulations.lib.
Require Import CoqOfRust.simulations.M.

Module AccountId.
  Inductive t : Set :=
  | Make (account_id : Z).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc1155::AccountId";
    φ '(Make x) :=
      Value.StructTuple "erc1155::AccountId" [Value.Integer Integer.U128 x];
  }.
End AccountId.

Module Env.
  Record t : Set := {
    caller : AccountId.t;
  }.
End Env.