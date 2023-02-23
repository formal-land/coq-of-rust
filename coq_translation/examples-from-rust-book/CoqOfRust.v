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

(** A generic class to represent methods by name. *)
Class Method (name : string) (T : Set) : Set := {
  method : T;
}.
Arguments method name {T Method}.

Module ExperimentsAroundMethods.
  Module Ty.
    Parameter t : Set.

    (** A class to the represent the associated functions of a given type. *)
    Class AssociatedFunction (name : string) (T : Set) : Set := {
      associated_function : T;
    }.
    Arguments associated_function name {T AssociatedFunction}.
  End Ty.

  Parameter foo : Ty.t -> bool.
  Parameter arg : Ty.t -> string.

  Global Instance Ty_foo : Ty.AssociatedFunction "foo" (Ty.t -> bool) := {|
    Ty.associated_function := foo;
  |}.

  Global Instance Ty_arg : Ty.AssociatedFunction "arg" (Ty.t -> string) := {|
    Ty.associated_function := arg;
  |}.

  Definition gre : Ty.t -> string := Ty.associated_function "arg".

  Global Instance explain : Method "explain" (Ty.t -> string) := {|
    method self := "hello";
  |}.

  Definition gre2 (ty : Ty.t) : string :=
    method "explain" ty ++ " world".
End ExperimentsAroundMethods.

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

Definition ref (A : Set) : Set := A.
Definition mut_ref : Set -> Set := ref.

Definition deref {A : Set} (r : ref A) : A := r.

Parameter eqb : forall {A : Set}, A -> A -> bool.

Parameter sub : Z -> Z -> Z.

Module IndexedField.
  Class Class (Self : Set) (index : Z) (T : Set) : Set := {
    get : Self -> T;
  }.

  Global Instance TupleOfSingleElement (T : Set)
    : IndexedField.Class T 0 T := {|
    get self := self;
  |}.
End IndexedField.

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

Module _crate.
  Module marker.
    Module Copy.
      Unset Primitive Projections.
      Class Class (Self : Set) : Set := {
      }.
      Global Set Primitive Projections.
    End Copy.
  End marker.

  Module clone.
    Module Clone.
      Class Class (Self : Set) : Set := {
        clone : ref Self -> Self;
      }.
    End Clone.
  End clone.

  Module io.
    Parameter _print : forall {A : Set}, A -> unit.
  End io.

  Module fmt.
    Module ImplArguments.
      Parameter new_v1 : forall {A B : Set}, A -> B -> unit.
      Parameter new_v1_formatted : forall {A B C : Set}, A -> B -> C -> unit.
    End ImplArguments.

    Module ImplArgumentV1.
      Parameter new_display : forall {A : Set}, A -> unit.
      Parameter new_binary : forall {A : Set}, A -> unit.
      Parameter new_octal : forall {A : Set}, A -> unit.
      Parameter new_lower_hex : forall {A : Set}, A -> unit.
    End ImplArgumentV1.
  End fmt.
End _crate.
