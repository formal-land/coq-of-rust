(* To avoid circular dependency
 * implementations of external traits are defined here
 *)

Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.core.result_types.
Require CoqOfRust.core.cmp.

(* derived implementation of PartialEq *)
Module Impl_PartialEq_for_Result.
  Parameter eq :
    forall `{State.Trait} {T E : Set}
      `{core.cmp.PartialEq.Trait T} `{core.cmp.PartialEq.Trait E},
      ref (Result T E) -> ref (Result T E) -> M bool.

  Global Instance I {T T_Rhs E E_Rhs : Set}
    `{State.Trait}
    {_ : core.cmp.PartialEq.Trait T (Rhs := T_Rhs)}
    {_ : core.cmp.PartialEq.Trait E (Rhs := E_Rhs)} :
    core.cmp.PartialEq.Trait (Result T E) (Rhs := _) := {
    eq := eq (T := T) (E := E);
  }.

  Global Instance Method_eq {T T_Rhs E E_Rhs : Set}
    `{State.Trait}
    {_ : core.cmp.PartialEq.Trait T (Rhs := T_Rhs)}
    {_ : core.cmp.PartialEq.Trait E (Rhs := E_Rhs)} :
    Notation.Dot "eq" := {|
    Notation.dot := eq (T := T) (E := E);
  |}.
End Impl_PartialEq_for_Result.

Module Impl_Result.
Section Impl_Result.
  Context `{State.Trait}.
  Context {T E : Set}.

  Definition Self : Set := Result T E.

  Parameter expect : Self -> string -> M T.

  Global Instance AF_expect : Notation.DoubleColon Self "expect" := {|
    Notation.double_colon := expect;
  |}.
End Impl_Result.
End Impl_Result.
