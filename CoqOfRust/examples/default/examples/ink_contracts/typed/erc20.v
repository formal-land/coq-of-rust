Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.typed.M.
Require CoqOfRust.examples.default.examples.ink_contracts.erc20.

Module Impl_erc20_Mapping_K_V.
  Parameter t : Set -> Set -> Set.

  Parameter get : forall {K V : Set}, Pointer.t (t K V) -> Pointer.t K -> M (option V).

  Parameter insert : forall {K V : Set}, Pointer.t (t K V) -> K -> V -> M unit.
End Impl_erc20_Mapping_K_V.
