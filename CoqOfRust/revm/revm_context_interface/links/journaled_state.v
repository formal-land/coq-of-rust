Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.revm.revm_context_interface.journaled_state.

(*
pub struct AccountLoad {
    pub load: Eip7702CodeLoad<()>,
    pub is_empty: bool,
}
*)
Module AccountLoad.
  Parameter t : Set.

  Global Instance IsLink : Link t.
  Admitted.
End AccountLoad.

(*
pub struct StateLoad<T> {
    pub data: T,
    pub is_cold: bool,
}
*)
Module StateLoad.
  Parameter t : forall (T : Set), Set.

  Global Instance IsLink {T : Set} `{Link T} : Link (t T).
  Admitted.
End StateLoad.

(*
pub struct Eip7702CodeLoad<T> {
    pub state_load: StateLoad<T>,
    pub is_delegate_account_cold: Option<bool>,
}
*)
Module Eip7702CodeLoad.
  Parameter t : forall (T : Set), Set.

  Global Instance IsLink {T : Set} `{Link T} : Link (t T).
  Admitted.
End Eip7702CodeLoad.
