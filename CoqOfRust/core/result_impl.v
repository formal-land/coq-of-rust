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

    Global Instance I
      {T E : Set} `{core.cmp.PartialEq.Trait T} `{core.cmp.PartialEq.Trait E} :
      core.cmp.PartialEq.Trait (Result T E) (Rhs := _) := {
      eq `{State.Trait} := eq (T := T) (E := E);
    }.

    Global Instance Method_eq `{State.Trait} {T E : Set}
    `{core.cmp.PartialEq.Trait T} `{core.cmp.PartialEq.Trait E} :
    Notation.Dot "eq" := {|
    Notation.dot := eq (T := T) (E := E);
  |}.
End Impl_PartialEq_for_Result.

Module Impl_Result.
Section Impl_Result.
  Context {T E : Set}.

  Definition Self : Set := Result T E.
  Arguments Self /.

  Parameter expect :
    forall `{H : State.Trait},
    Self -> ref str -> M (H := H) T.

  Global Instance Method_expect `{State.Trait} :
    Notation.Dot "expect" := {|
    Notation.dot := expect;
  |}.
End Impl_Result.
End Impl_Result.
