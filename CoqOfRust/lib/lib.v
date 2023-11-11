Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.

(* Global settings for files importing this file *)
Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope list_scope.
Global Open Scope string_scope.
Global Open Scope Z_scope.
Global Open Scope type_scope.

Export List.ListNotations.

Require Export CoqOfRust.M.
Export M.Notations.

Module Notation.
  (** A class to represent the notation [e1.e2]. This is mainly used to call
      methods, or access to named or indexed fields of structures. *)
  Class Dot (name : string) {T : Set} : Set := {
    dot : T;
  }.
  Arguments dot name {T Dot}.

  (** A class to represent associated functions (the notation [e1::e2]). The
      kind might be [Set] functions associated to a type, or [Set -> Set] for
      functions associated to a trait. *)
  Class DoubleColon {Kind : Type} (type : Kind) (name : string) {T : Set} :
    Set := {
    double_colon : T;
  }.
  Arguments double_colon {Kind} type name {T DoubleColon}.

  (* A class to represent types in a trait. *)
  Class DoubleColonType {Kind : Type} (type : Kind) (name : string) : Type := {
    double_colon_type : Set;
  }.
  Arguments double_colon_type {Kind} type name {DoubleColonType}.
End Notation.

(** Note that we revert the arguments in this notation. *)
Notation "e1 .[ e2 ]" := (Notation.dot e2 e1)
  (at level 0).

Notation "e1 ::[ e2 ]" := (Notation.double_colon e1 e2)
  (at level 0).

(** A method is also an associated function for its type. *)
Global Instance AssociatedFunctionFromMethod
  (type : Set) (name : string) (T : Set)
  `(Notation.Dot name (T := type -> T)) :
  Notation.DoubleColon type name (T := type -> T) := {
  Notation.double_colon := Notation.dot name;
}.

Definition defaultType (T : option Set) (Default : Set) : Set :=
  match T with
  | Some T => T
  | None => Default
  end.

Parameter axiom : forall {A : Set}, A.

Parameter cast : forall {A : Set}, A -> forall (B : Set), B.

Parameter sequence : forall {A B : Set}, A -> B -> B.

Notation "e1 ;; e2" := (sequence e1 e2)
  (at level 61, right associativity).

Parameter assign : forall {A : Set}, A -> A -> unit.

Definition unit : Set := Datatypes.unit.
Module bool.
  Definition t : Set := bool.
End bool.

Definition u8 : Set := Z.
Definition u16 : Set := Z.

Module u32.
  Definition t : Set := Z.
End u32.
Definition u32 : Set := u32.t.

Definition u64 : Set := Z.

Module u128.
  Definition t : Set := Z.
End u128.

Definition usize : Set := Z.

Definition i8 : Set := Z.
Definition i16 : Set := Z.
Definition i32 : Set := Z.
Definition i64 : Set := Z.
Definition i128 : Set := Z.
Definition isize : Set := Z.

(* We approximate floating point numbers with integers *)
Definition f32 : Set := Z.
Definition f64 : Set := Z.

Definition str : Set := Coq.Strings.String.string.
Definition char : Set := Coq.Strings.Ascii.ascii.

Definition ref (A : Set) : Set := M.Val A.
Definition mut_ref (A : Set) : Set := M.Val A.

Definition slice (A : Set) : Set := list A.
Definition array (A : Set) : Set := list A.

Module never.
  Definition t : Set := Empty_set.
End never.

Definition never_to_any {A B : Set} (x : A) : M B :=
  M.impossible.

Definition use {A : Set} (x : A) : M A := M.pure x.

Definition mk_str (s : Coq.Strings.String.string) : M.Val (ref str) :=
  M.Ref.Immutable (M.Ref.Immutable s).

Module UnOp.
  Parameter not : bool -> M bool.
  Parameter neg : forall {A : Set}, A -> M A.
End UnOp.

Module BinOp.
  Parameter add : forall {A : Set}, A -> A -> M A.
  Parameter sub : forall {A : Set}, A -> A -> M A.
  Parameter mul : forall {A : Set}, A -> A -> M A.
  Parameter div : forall {A : Set}, A -> A -> M A.
  Parameter rem : forall {A : Set}, A -> A -> M A.
  Parameter bit_xor : forall {A : Set}, A -> A -> M A.
  Parameter bit_and : forall {A : Set}, A -> A -> M A.
  Parameter bit_or : forall {A : Set}, A -> A -> M A.
  Parameter shl : forall {A : Set}, A -> A -> M A.
  Parameter shr : forall {A : Set}, A -> A -> M A.

  Parameter eq : forall {A : Set}, A -> A -> M (M.Val bool.t).
  Parameter ne : forall {A : Set}, A -> A -> M (M.Val bool.t).

  Parameter lt : forall {A : Set}, A -> A -> M (M.Val bool.t).
  Parameter le : forall {A : Set}, A -> A -> M (M.Val bool.t).
  Parameter ge : forall {A : Set}, A -> A -> M (M.Val bool.t).
  Parameter gt : forall {A : Set}, A -> A -> M (M.Val bool.t).

  Parameter and : forall {A : Set}, A -> A -> M (M.Val bool.t).
  Parameter or : forall {A : Set}, A -> A -> M (M.Val bool.t).
End BinOp.
