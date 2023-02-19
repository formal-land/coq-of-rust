Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.

(* Global settings for files importing this file *)
Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope string_scope.
Global Open Scope Z_scope.
Global Open Scope type_scope.

Export List.ListNotations.

Parameter axiom : forall {A : Set}, A.

Notation "e1 ;; e2" := (let '_ := e1 in e2)
  (at level 61, right associativity).

Definition u8 : Set := Z.
Definition u16 : Set := Z.
Definition u32 : Set := Z.
Definition u64 : Set := Z.
Definition u128 : Set := Z.

Definition i8 : Set := Z.
Definition i16 : Set := Z.
Definition i32 : Set := Z.
Definition i64 : Set := Z.
Definition i128 : Set := Z.

(* We approximate floating point numbers with integers *)
Definition f32 : Set := Z.
Definition f64 : Set := Z.

Definition static_ref (A : Set) : Set := A.
Definition mut_ref (A : Set) : Set := A.

Module std.
  Module result.
    Module Result.
      Inductive t (T E : Set) : Set :=
      | Ok : T -> t T E
      | Err : E -> t T E.
      Arguments Ok {T E} _.
      Arguments Err {T E} _.
    End Result.
    Definition Result := Result.t.
  End result.

  Module fmt.
    Parameter Formatter : Set.
    Parameter Error : Set.

    Definition Result : Set := result.Result unit Error.

    Module Display.
      Class Class (Self : Set) : Set := {
        fmt : Self -> mut_ref Formatter -> Result;
      }.
    End Display.
  End fmt.
End std.
