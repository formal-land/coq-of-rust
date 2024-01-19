(* To avoid circular dependency
 * implementations of external traits are defined here
 *)

Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.core.result_types.
Require CoqOfRust.core.cmp.

(* derived implementation of PartialEq *)
Module Impl_PartialEq_for_Result.
  Parameter eq :
    forall {T E : Set}
      `{core.cmp.PartialEq.Trait T} `{core.cmp.PartialEq.Trait E},
      ref (Result.t T E) ->
      ref (Result.t T E) ->
      M bool.

  Global Instance I {T T_Rhs E E_Rhs : Set}
    {_ : core.cmp.PartialEq.Trait T (Rhs := T_Rhs)}
    {_ : core.cmp.PartialEq.Trait E (Rhs := E_Rhs)} :
    core.cmp.PartialEq.Required.Trait (Result.t T E) (Rhs := _) := {
    eq := eq (T := T) (E := E);
    ne := Datatypes.None;
  }.
End Impl_PartialEq_for_Result.

Module Impl_Result.
Section Impl_Result.
  Context {T E : Set}.

  Definition Self : Set := Result.t T E.

  (*
  pub fn expect(self, msg: &str) -> T
  where
      E: Debug,
  *)
  Parameter expect : Self -> ref str.t -> M T.

  Global Instance AF_expect : Notations.DoubleColon Self "expect" := {|
    Notations.double_colon := expect;
  |}.

  (*
  pub const fn is_err(&self) -> bool
  *)
  Parameter is_err : ref Self -> M bool.

  Global Instance AF_is_err : Notations.DoubleColon Self "is_err" := {|
    Notations.double_colon := is_err;
  |}.

  (*
  pub fn map<U, F>(self, op: F) -> Result<U, E>
  where
      F: FnOnce(T) -> U,
  *)
  Parameter map : forall {U : Set},
    Self -> (T -> M U) -> M (Result.t U E).

  Global Instance AF_map {U : Set} :
      Notations.DoubleColon Self "map" := {|
    Notations.double_colon := map (U := U);
  |}.

  (*
  pub fn map_err<F, O>(self, op: O) -> Result<T, F>
  where
    O: FnOnce(E) -> F,
  *)
  Parameter map_err : forall {F : Set},
    Self -> (E -> M F) -> M (Result.t T F).

  Global Instance AF_map_err {F : Set} :
      Notations.DoubleColon Self "map_err" := {|
    Notations.double_colon := map_err (F := F);
  |}.

  (*
  pub fn unwrap(self) -> T
  where
    E: Debug,
  *)
  Parameter unwrap : Self -> M T.

  Global Instance AF_unwrap : Notations.DoubleColon Self "unwrap" := {|
    Notations.double_colon := unwrap;
  |}.

  (* pub fn unwrap_or_else<F: FnOnce(E) -> T>(self, op: F) -> T *)
  Parameter unwrap_or_else : Self -> (E -> M T) -> M T.

  Global Instance AF_unwrap_or_else :
      Notations.DoubleColon Self "unwrap_or_else" := {|
    Notations.double_colon := unwrap_or_else;
  |}.

  (*
  pub fn and_then<U, F>(self, op: F) -> Result<U, E>
  where
      F: FnOnce(T) -> Result<U, E>,
  *)
  Parameter and_then : forall {U : Set},
    Self -> (T -> M (Result.t U E)) -> M (Result.t U E).

  Global Instance AF_and_then {U : Set} :
      Notations.DoubleColon Self "and_then" := {|
    Notations.double_colon := and_then (U := U);
  |}.

  (*
  pub fn unwrap_err(self) -> E
  where
      T: Debug,
  *)
  Parameter unwrap_err : Self -> M E.

  Global Instance AF_unwrap_err :
      Notations.DoubleColon Self "unwrap_err" := {|
    Notations.double_colon := unwrap_err;
  |}.

  (* pub const fn is_ok(&self) -> bool *)
  Parameter is_ok : ref Self -> M bool.

  Global Instance AF_is_ok : Notations.DoubleColon Self "is_ok" := {|
    Notations.double_colon := is_ok;
  |}.

  (* pub fn ok(self) -> Option<T> *)
  Parameter ok : Self -> M (option.Option.t T).

  Global Instance AF_ok : Notations.DoubleColon Self "ok" := {|
    Notations.double_colon := ok;
  |}.
End Impl_Result.
End Impl_Result.

Module  Impl_Option.
Section Impl_Option.
  Context {T : Set}.
  Definition Self : Set := option.Option.t T.

  (* pub fn ok_or<E>(self, err: E) -> Result<T, E> *)
  Parameter ok_or : forall {E : Set}, Self -> E -> M (Result.t T E).

  Global Instance AF_ok_or {E : Set} : Notations.DoubleColon Self "ok_or" := {
    Notations.double_colon := ok_or (E := E);
  }.

  (*
  pub fn ok_or_else<E, F>(self, err: F) -> Result<T, E>
  where
      F: FnOnce() -> E,
  *)
  Parameter ok_or_else : forall {E F : Set}, Self -> F -> M (Result.t T E).

  Global Instance AF_ok_or_else {E F : Set} :
      Notations.DoubleColon Self "ok_or_else" := {
    Notations.double_colon := ok_or_else (E := E) (F := F);
  }.
End Impl_Option.
End Impl_Option.
