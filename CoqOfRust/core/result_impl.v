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

  Parameter expect : Self -> string -> M T.

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
End Impl_Result.
End Impl_Result.

