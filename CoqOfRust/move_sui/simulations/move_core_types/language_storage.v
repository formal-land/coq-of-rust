Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.

Import simulations.M.Notations.

(*
pub struct ModuleId {
    address: AccountAddress,
    name: Identifier,
}
*)
Module ModuleId.
  Parameter t : Set.
End ModuleId.
