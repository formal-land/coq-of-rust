Require Import CoqOfRust.lib.lib.

Require CoqOfRust.core.default.

(* ********STRUCTS******** *)
(*
[x] IntoIter
[x] Iter
[x] IterMut
*)

(* pub struct IntoIter<A> { /* private fields */ } *)
Module IntoIter.
  Parameter t : Set -> Set.
End IntoIter.

(*
pub struct Iter<'a, A>
where
    A: 'a,
{ /* private fields */ }
*)
Module Iter.
  Parameter t : Set -> Set.
End Iter.

(* pub struct IterMut<'a, A>
where
    A: 'a,
{ /* private fields */ } *)
Module IterMut.
  Parameter t : Set -> Set.
End IterMut.


(* ********ENUMS******** *)
(*
[x] Option
*)

Module Option.
  Inductive t (T : Set) : Set :=
  | None : t T
  | Some : T -> t T.
  Arguments None {_}.
  Arguments Some {_}.

  Definition Get_Some_0 {T : Set} :=
    Ref.map (Big := t T)
      (fun α =>
        match α with
        | Some α0 => Datatypes.Some α0
        | _ => Datatypes.None
        end)
      (fun β α =>
        match α with
        | Some _ => Datatypes.Some (Some β)
        | _ => Datatypes.None
        end).
End Option.

Module Impl_Option. Section Impl_Option.
  Context {T : Set}.

  Definition Self : Set := Option.t T.

  (* pub fn expect(self, msg: &str) -> T *)
  Parameter expect : Self -> ref str.t -> M T.

  Global Instance AF_expect : Notations.DoubleColon Self "expect" := {
    Notations.double_colon := expect;
  }.

  Definition unwrap_or_default {H0 : core.default.Default.Trait T}
      (self : Self) : M T :=
    match self with
    | Option.None => core.default.Default.default (Self := T)
    | Option.Some x => M.pure x
    end.

  Global Instance AF_unwrap_or_default {H0 : core.default.Default.Trait T} :
    Notations.DoubleColon Self "unwrap_or_default" := {
    Notations.double_colon := unwrap_or_default;
  }.

  Definition unwrap_or (self : Self) (default : T) : M T :=
    match self with
    | Option.None => M.pure default
    | Option.Some x => M.pure x
    end.

  Global Instance AF_unwrap_or : Notations.DoubleColon Self "unwrap_or" := {
    Notations.double_colon := unwrap_or;
  }.

  (* pub const fn is_some(&self) -> bool *)
  Definition is_some (self : ref Self) : M bool :=
    let* self := M.read self in
    match self with
    | Option.Some _ => M.pure true
    | Option.None => M.pure false
    end.

  Global Instance AF_is_some : Notations.DoubleColon Self "is_some" := {
    Notations.double_colon := is_some;
  }.

  (*
  pub fn map<U, F>(self, f: F) -> Option<U>
  where
      F: FnOnce(T) -> U,
  *)
  Parameter map : forall {U : Set}, Self -> (T -> M U) -> M (option.Option.t U).

  Global Instance AF_map {U : Set} : Notations.DoubleColon Self "map" := {
    Notations.double_colon := map (U := U);
  }.

  (*
  pub fn and_then<U, F>(self, f: F) -> Option<U>
  where
      F: FnOnce(T) -> Option<U>,
  *)
  Parameter and_then :
    forall {U : Set},
    Self -> (T -> M (option.Option.t U)) -> M (option.Option.t U).

  Global Instance AF_and_then {U : Set} :
    Notations.DoubleColon Self "and_then" := {
    Notations.double_colon := and_then (U := U);
  }.

  (* pub fn get_or_insert(&mut self, value: T) -> &mut T *)
  Parameter get_or_insert : mut_ref Self -> T -> M (mut_ref T).

  Global Instance AF_get_or_insert :
      Notations.DoubleColon Self "get_or_insert" := {
    Notations.double_colon := get_or_insert;
  }.

  Global Instance I_Default {ℋ : default.Default.Trait T} :
    default.Default.Trait (core.option.Option.t T).
  Admitted.

  Global Instance I_Clone {ℋ : clone.Clone.Trait T} :
    clone.Clone.Trait (core.option.Option.t T).
  Admitted.
End Impl_Option. End Impl_Option.
