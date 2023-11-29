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

Module Notations.
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
End Notations.

(** Note that we revert the arguments in this notation. *)
Notation "e1 .[ e2 ]" := (Notations.dot e2 e1)
  (at level 0).

Notation "e1 ::[ e2 ]" := (Notations.double_colon e1 e2)
  (at level 0).

Notation "e1 ::type[ e2 ]" := (Notations.double_colon_type e1 e2)
  (at level 0).

(** A method is also an associated function for its type. *)
Global Instance AssociatedFunctionFromMethod
  (type : Set) (name : string) (T : Set)
  `(Notations.Dot name (T := type -> T)) :
  Notations.DoubleColon type name (T := type -> T) := {
  Notations.double_colon := Notations.dot name;
}.

Definition defaultType (T : option Set) (Default : Set) : Set :=
  match T with
  | Some T => T
  | None => Default
  end.

Parameter axiom : forall {A : Set}, A.

Definition assign {A : Set} (target : M.Val A) (source : A) : M (M.Val unit) :=
  let* _ := M.write target source in
  M.alloc tt.

Module bool.
  Definition t : Set := bool.
End bool.

(** ** Integer types *)
(** We distinguish all integer types for the type-class inference. *)

Module u8.
  Inductive t : Set := Make (z : Z) : t.
End u8.

Module u16.
  Inductive t : Set := Make (z : Z) : t.
End u16.

Module u32.
  Inductive t : Set := Make (z : Z) : t.
End u32.

Module u64.
  Inductive t : Set := Make (z : Z) : t.
End u64.

Module u128.
  Inductive t : Set := Make (z : Z) : t.
End u128.

Module usize.
  Inductive t : Set := Make (z : Z) : t.
End usize.

Module i8.
  Inductive t : Set := Make (z : Z) : t.
End i8.

Module i16.
  Inductive t : Set := Make (z : Z) : t.
End i16.

Module i32.
  Inductive t : Set := Make (z : Z) : t.
End i32.

Module i64.
  Inductive t : Set := Make (z : Z) : t.
End i64.

Module i128.
  Inductive t : Set := Make (z : Z) : t.
End i128.

Module isize.
  Inductive t : Set := Make (z : Z) : t.
End isize.

(* We approximate floating point numbers with integers *)
Module f32.
  Inductive t : Set := Make (z : Z) : t.
End f32.

Module f64.
  Inductive t : Set := Make (z : Z) : t.
End f64.

Module str.
  Definition t : Set := Coq.Strings.String.string.
End str.

Module char.
  Definition t : Set := Coq.Strings.Ascii.ascii.
End char.

Definition ref (A : Set) : Set := M.Val A.
Definition mut_ref (A : Set) : Set := M.Val A.

Definition slice (A : Set) : Set := list A.
Definition array (A : Set) : Set := list A.

Module never.
  Definition t : Set := Empty_set.
End never.

Definition never_to_any {A B : Set} (x : A) : M B :=
  M.impossible.

Definition use {A : Set} (x : A) : A := x.

Definition mk_str (s : Coq.Strings.String.string) : M.Val (ref str.t) :=
  M.Ref.Imm (M.Ref.Imm s).

Module Integer.
  Class C (Self : Set) : Set := {
    to_Z : Self -> Z;
    of_Z : Z -> Self;
    (** Apply the modulo operation in case of overflows. *)
    normalize_wrap : Z -> Z;
    min : Z;
    max : Z;
  }.

  Definition normalize_option {Self : Set} `{C Self} (z : Z) : option Self :=
    if z <? min then
      None
    else if max <? z then
      None
    else
      Some (of_Z z).

  Definition normalize_panic {Self : Set} `{C Self} (z : Z) : M Self :=
    match normalize_option z with
    | None => M.panic "integer over/underflow"
    | Some x => M.pure x
    end.

  Global Instance I_u8 : C u8.t := {
    to_Z '(u8.Make z) := z;
    of_Z z := u8.Make z;
    normalize_wrap z := Z.modulo z 2^8;
    min := 0;
    max := 2^8 - 1;
  }.

  Global Instance I_u16 : C u16.t := {
    to_Z '(u16.Make z) := z;
    of_Z z := u16.Make z;
    normalize_wrap z := Z.modulo z 2^16;
    min := 0;
    max := 2^16 - 1;
  }.

  Global Instance I_u32 : C u32.t := {
    to_Z '(u32.Make z) := z;
    of_Z z := u32.Make z;
    normalize_wrap z := Z.modulo z 2^32;
    min := 0;
    max := 2^32 - 1;
  }.

  Global Instance I_u64 : C u64.t := {
    to_Z '(u64.Make z) := z;
    of_Z z := u64.Make z;
    normalize_wrap z := Z.modulo z 2^64;
    min := 0;
    max := 2^64 - 1;
  }.

  Global Instance I_u128 : C u128.t := {
    to_Z '(u128.Make z) := z;
    of_Z z := u128.Make z;
    normalize_wrap z := Z.modulo z 2^128;
    min := 0;
    max := 2^128 - 1;
  }.

  Global Instance I_usize : C usize.t := {
    to_Z '(usize.Make z) := z;
    of_Z z := usize.Make z;
    normalize_wrap z := Z.modulo z 2^64;
    min := 0;
    max := 2^64 - 1;
  }.

  Global Instance I_i8 : C i8.t := {
    to_Z '(i8.Make z) := z;
    of_Z z := i8.Make z;
    normalize_wrap z := Z.modulo (z + 2^7) 2^8 - 2^7;
    min := -2^7;
    max := 2^7 - 1;
  }.

  Global Instance I_i16 : C i16.t := {
    to_Z '(i16.Make z) := z;
    of_Z z := i16.Make z;
    normalize_wrap z := Z.modulo (z + 2^15) 2^16 - 2^15;
    min := -2^15;
    max := 2^15 - 1;
  }.

  Global Instance I_i32 : C i32.t := {
    to_Z '(i32.Make z) := z;
    of_Z z := i32.Make z;
    normalize_wrap z := Z.modulo (z + 2^31) 2^32 - 2^31;
    min := -2^31;
    max := 2^31 - 1;
  }.

  Global Instance I_i64 : C i64.t := {
    to_Z '(i64.Make z) := z;
    of_Z z := i64.Make z;
    normalize_wrap z := Z.modulo (z + 2^63) 2^64 - 2^63;
    min := -2^63;
    max := 2^63 - 1;
  }.

  Global Instance I_i128 : C i128.t := {
    to_Z '(i128.Make z) := z;
    of_Z z := i128.Make z;
    normalize_wrap z := Z.modulo (z + 2^127) 2^128 - 2^127;
    min := -2^127;
    max := 2^127 - 1;
  }.

  Global Instance I_isize : C isize.t := {
    to_Z '(isize.Make z) := z;
    of_Z z := isize.Make z;
    normalize_wrap z := Z.modulo (z + 2^63) 2^64 - 2^63;
    min := -2^63;
    max := 2^63 - 1;
  }.
End Integer.

Module UnOp.
  Parameter not : bool -> bool.
  Parameter neg : forall {A : Set}, A -> M A.
End UnOp.

Module BinOp.
  Module Pure.
    Parameter bit_xor : forall {A : Set}, A -> A -> A.
    Parameter bit_and : forall {A : Set}, A -> A -> A.
    Parameter bit_or : forall {A : Set}, A -> A -> A.

    Definition make_comparison {A : Set} `{Integer.C A}
      (bin_op : Z -> Z -> bool)
      (v1 v2 : A) :
      bool.t :=
    let z1 := Integer.to_Z v1 in
    let z2 := Integer.to_Z v2 in
    bin_op z1 z2.

    Definition eq {A : Set} `{Integer.C A} : A -> A -> bool.t :=
      make_comparison Z.eqb.

    Definition ne {A : Set} `{Integer.C A} : A -> A -> bool.t :=
      make_comparison (fun z1 z2 => negb (Z.eqb z1 z2)).

    Definition lt {A : Set} `{Integer.C A} : A -> A -> bool.t :=
      make_comparison Z.ltb.

    Definition le {A : Set} `{Integer.C A} : A -> A -> bool.t :=
      make_comparison Z.leb.

    Definition ge {A : Set} `{Integer.C A} : A -> A -> bool.t :=
      make_comparison Z.geb.

    Definition gt {A : Set} `{Integer.C A} : A -> A -> bool.t :=
      make_comparison Z.gtb.

    Parameter and : forall {A : Set}, A -> A -> bool.t.
    Parameter or : forall {A : Set}, A -> A -> bool.t.
  End Pure.

  Module Option.
    Definition make_arithmetic {A : Set} `{Integer.C A}
        (bin_op : Z -> Z -> Z)
        (v1 v2 : A) :
        option A :=
      let z1 := Integer.to_Z v1 in
      let z2 := Integer.to_Z v2 in
      Integer.normalize_option (bin_op z1 z2).

    Definition add {A : Set} `{Integer.C A} (v1 v2 : A) : option A :=
      make_arithmetic Z.add v1 v2.

    Definition sub {A : Set} `{Integer.C A} (v1 v2 : A) : option A :=
      make_arithmetic Z.sub v1 v2.

    Definition mul {A : Set} `{Integer.C A} (v1 v2 : A) : option A :=
      make_arithmetic Z.mul v1 v2.

    Parameter div : forall {A : Set}, A -> A -> option A.
    Parameter rem : forall {A : Set}, A -> A -> option A.
    
    Parameter shl : forall {A : Set}, A -> A -> option A.
    Parameter shr : forall {A : Set}, A -> A -> option A.
  End Option.

  Module Panic.
    Definition make_arithmetic {A : Set} `{Integer.C A}
        (bin_op : Z -> Z -> Z)
        (v1 v2 : A) :
        M A :=
      let z1 := Integer.to_Z v1 in
      let z2 := Integer.to_Z v2 in
      Integer.normalize_panic (bin_op z1 z2).

    Definition add {A : Set} `{Integer.C A} (v1 v2 : A) : M A :=
      make_arithmetic Z.add v1 v2.

    Definition sub {A : Set} `{Integer.C A} (v1 v2 : A) : M A :=
      make_arithmetic Z.sub v1 v2.

    Definition mul {A : Set} `{Integer.C A} (v1 v2 : A) : M A :=
      make_arithmetic Z.mul v1 v2.

    Parameter div : forall {A : Set}, A -> A -> M A.
    Parameter rem : forall {A : Set}, A -> A -> M A.
    
    Parameter shl : forall {A : Set}, A -> A -> M A.
    Parameter shr : forall {A : Set}, A -> A -> M A.
  End Panic.

  Module Wrap.
    Definition make_arithmetic {A : Set} `{Integer.C A}
        (bin_op : Z -> Z -> Z)
        (v1 v2 : A) :
        A :=
      let z1 := Integer.to_Z v1 in
      let z2 := Integer.to_Z v2 in
      let z := Integer.normalize_wrap (bin_op z1 z2) in
      Integer.of_Z z.

    Definition add {A : Set} `{Integer.C A} (v1 v2 : A) : A :=
      make_arithmetic Z.add v1 v2.

    Definition sub {A : Set} `{Integer.C A} (v1 v2 : A) : A :=
      make_arithmetic Z.sub v1 v2.

    Definition mul {A : Set} `{Integer.C A} (v1 v2 : A) : A :=
      make_arithmetic Z.mul v1 v2.

    Parameter div : forall {A : Set}, A -> A -> A.
    Parameter rem : forall {A : Set}, A -> A -> A.
    
    Parameter shl : forall {A : Set}, A -> A -> A.
    Parameter shr : forall {A : Set}, A -> A -> A.
  End Wrap.

  Module Optimistic.
    Definition make_arithmetic {A : Set} `{Integer.C A}
        (bin_op : Z -> Z -> Z)
        (v1 v2 : A) :
        A :=
      let z1 := Integer.to_Z v1 in
      let z2 := Integer.to_Z v2 in
      let z := bin_op z1 z2 in
      Integer.of_Z z.

    Definition add {A : Set} `{Integer.C A} (v1 v2 : A) : A :=
      make_arithmetic Z.add v1 v2.

    Definition sub {A : Set} `{Integer.C A} (v1 v2 : A) : A :=
      make_arithmetic Z.sub v1 v2.

    Definition mul {A : Set} `{Integer.C A} (v1 v2 : A) : A :=
      make_arithmetic Z.mul v1 v2.

    Parameter div : forall {A : Set}, A -> A -> A.
    Parameter rem : forall {A : Set}, A -> A -> A.
    
    Parameter shl : forall {A : Set}, A -> A -> A.
    Parameter shr : forall {A : Set}, A -> A -> A.
  End Optimistic.
End BinOp.

(** ** Integer notations *)

Infix "==u8" := (BinOp.Pure.eq (A := u8.t)) (at level 60).
Infix "!=u8" := (BinOp.Pure.ne (A := u8.t)) (at level 60).
Infix "<u8" := (BinOp.Pure.lt (A := u8.t)) (at level 60).
Infix "<=u8" := (BinOp.Pure.le (A := u8.t)) (at level 60).
Infix ">=u8" := (BinOp.Pure.ge (A := u8.t)) (at level 60).
Infix ">u8" := (BinOp.Pure.gt (A := u8.t)) (at level 60).

Infix "==u16" := (BinOp.Pure.eq (A := u16.t)) (at level 60).
Infix "!=u16" := (BinOp.Pure.ne (A := u16.t)) (at level 60).
Infix "<u16" := (BinOp.Pure.lt (A := u16.t)) (at level 60).
Infix "<=u16" := (BinOp.Pure.le (A := u16.t)) (at level 60).
Infix ">=u16" := (BinOp.Pure.ge (A := u16.t)) (at level 60).
Infix ">u16" := (BinOp.Pure.gt (A := u16.t)) (at level 60).

Infix "==u32" := (BinOp.Pure.eq (A := u32.t)) (at level 60).
Infix "!=u32" := (BinOp.Pure.ne (A := u32.t)) (at level 60).
Infix "<u32" := (BinOp.Pure.lt (A := u32.t)) (at level 60).
Infix "<=u32" := (BinOp.Pure.le (A := u32.t)) (at level 60).
Infix ">=u32" := (BinOp.Pure.ge (A := u32.t)) (at level 60).
Infix ">u32" := (BinOp.Pure.gt (A := u32.t)) (at level 60).

Infix "==u64" := (BinOp.Pure.eq (A := u64.t)) (at level 60).
Infix "!=u64" := (BinOp.Pure.ne (A := u64.t)) (at level 60).
Infix "<u64" := (BinOp.Pure.lt (A := u64.t)) (at level 60).
Infix "<=u64" := (BinOp.Pure.le (A := u64.t)) (at level 60).
Infix ">=u64" := (BinOp.Pure.ge (A := u64.t)) (at level 60).
Infix ">u64" := (BinOp.Pure.gt (A := u64.t)) (at level 60).

Infix "==u128" := (BinOp.Pure.eq (A := u128.t)) (at level 60).
Infix "!=u128" := (BinOp.Pure.ne (A := u128.t)) (at level 60).
Infix "<u128" := (BinOp.Pure.lt (A := u128.t)) (at level 60).
Infix "<=u128" := (BinOp.Pure.le (A := u128.t)) (at level 60).
Infix ">=u128" := (BinOp.Pure.ge (A := u128.t)) (at level 60).
Infix ">u128" := (BinOp.Pure.gt (A := u128.t)) (at level 60).

Infix "==usize" := (BinOp.Pure.eq (A := usize.t)) (at level 60).
Infix "!=usize" := (BinOp.Pure.ne (A := usize.t)) (at level 60).
Infix "<usize" := (BinOp.Pure.lt (A := usize.t)) (at level 60).
Infix "<=usize" := (BinOp.Pure.le (A := usize.t)) (at level 60).
Infix ">=usize" := (BinOp.Pure.ge (A := usize.t)) (at level 60).
Infix ">usize" := (BinOp.Pure.gt (A := usize.t)) (at level 60).

Infix "==i8" := (BinOp.Pure.eq (A := i8.t)) (at level 60).
Infix "!=i8" := (BinOp.Pure.ne (A := i8.t)) (at level 60).
Infix "<i8" := (BinOp.Pure.lt (A := i8.t)) (at level 60).
Infix "<=i8" := (BinOp.Pure.le (A := i8.t)) (at level 60).
Infix ">=i8" := (BinOp.Pure.ge (A := i8.t)) (at level 60).
Infix ">i8" := (BinOp.Pure.gt (A := i8.t)) (at level 60).

Infix "==i16" := (BinOp.Pure.eq (A := i16.t)) (at level 60).
Infix "!=i16" := (BinOp.Pure.ne (A := i16.t)) (at level 60).
Infix "<i16" := (BinOp.Pure.lt (A := i16.t)) (at level 60).
Infix "<=i16" := (BinOp.Pure.le (A := i16.t)) (at level 60).
Infix ">=i16" := (BinOp.Pure.ge (A := i16.t)) (at level 60).
Infix ">i16" := (BinOp.Pure.gt (A := i16.t)) (at level 60).

Infix "==i32" := (BinOp.Pure.eq (A := i32.t)) (at level 60).
Infix "!=i32" := (BinOp.Pure.ne (A := i32.t)) (at level 60).
Infix "<i32" := (BinOp.Pure.lt (A := i32.t)) (at level 60).
Infix "<=i32" := (BinOp.Pure.le (A := i32.t)) (at level 60).
Infix ">=i32" := (BinOp.Pure.ge (A := i32.t)) (at level 60).
Infix ">i32" := (BinOp.Pure.gt (A := i32.t)) (at level 60).

Infix "==i64" := (BinOp.Pure.eq (A := i64.t)) (at level 60).
Infix "!=i64" := (BinOp.Pure.ne (A := i64.t)) (at level 60).
Infix "<i64" := (BinOp.Pure.lt (A := i64.t)) (at level 60).
Infix "<=i64" := (BinOp.Pure.le (A := i64.t)) (at level 60).
Infix ">=i64" := (BinOp.Pure.ge (A := i64.t)) (at level 60).
Infix ">i64" := (BinOp.Pure.gt (A := i64.t)) (at level 60).

Infix "==i128" := (BinOp.Pure.eq (A := i128.t)) (at level 60).
Infix "!=i128" := (BinOp.Pure.ne (A := i128.t)) (at level 60).
Infix "<i128" := (BinOp.Pure.lt (A := i128.t)) (at level 60).
Infix "<=i128" := (BinOp.Pure.le (A := i128.t)) (at level 60).
Infix ">=i128" := (BinOp.Pure.ge (A := i128.t)) (at level 60).
Infix ">i128" := (BinOp.Pure.gt (A := i128.t)) (at level 60).

Infix "==isize" := (BinOp.Pure.eq (A := isize.t)) (at level 60).
Infix "!=isize" := (BinOp.Pure.ne (A := isize.t)) (at level 60).
Infix "<isize" := (BinOp.Pure.lt (A := isize.t)) (at level 60).
Infix "<=isize" := (BinOp.Pure.le (A := isize.t)) (at level 60).
Infix ">=isize" := (BinOp.Pure.ge (A := isize.t)) (at level 60).
Infix ">isize" := (BinOp.Pure.gt (A := isize.t)) (at level 60).
