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
      M.Val (ref (Result T E)) ->
      M.Val (ref (Result T E)) ->
      M (M.Val bool).

  Global Instance I {T T_Rhs E E_Rhs : Set}
    {_ : core.cmp.PartialEq.Trait T (Rhs := T_Rhs)}
    {_ : core.cmp.PartialEq.Trait E (Rhs := E_Rhs)} :
    core.cmp.PartialEq.Required.Trait (Result T E) (Rhs := _) := {
    eq := eq (T := T) (E := E);
    ne := Datatypes.None;
  }.
End Impl_PartialEq_for_Result.

Module Impl_Result.
Section Impl_Result.
  Context {T E : Set}.

  Definition Self : Set := Result T E.

  Parameter expect : Self -> string -> M T.

  Global Instance AF_expect : Notation.DoubleColon Self "expect" := {|
    Notation.double_colon := expect;
  |}.
End Impl_Result.
End Impl_Result.
