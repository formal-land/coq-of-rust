Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Export CoqOfRust.RecordUpdate.

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

Notation "ty ::[ name ]" := (M.associated_function ty name)
  (at level 0).

(* Notation "e1 ::type[ e2 ]" := (Notations.double_colon_type e1 e2)
  (at level 0). *)

Parameter axiom : forall {A : Set}, A.

Definition assign (target : Value.t) (source : Value.t) : M :=
  let* _ := M.write target source in
  M.alloc (Value.Tuple []).

(** ** Integer types *)

Definition never_to_any (x : Value.t) : M :=
  M.impossible.

Definition use (x : Value.t) : Value.t :=
  x.

(** A value with an address of type `ref str`. *)
Definition mk_str (s : string) : Value.t :=
  Value.Pointer (Pointer.Immediate (
    Value.Pointer (Pointer.Immediate (
      Value.String s
    ))
  )).

Module IntegerDescription.
  Class C (Self : M.Integer.t) : Set := {
    (** Apply the modulo operation in case of overflows. *)
    normalize_wrap : Z -> Z;
    min : Z;
    max : Z;
  }.
End IntegerDescription.

Module Integer.
  Class C (Self : M.Integer.t) : Set := {
    (** Apply the modulo operation in case of overflows. *)
    normalize_wrap : Z -> Z;
    min : Z;
    max : Z;
  }.

  Definition normalize_error {Self : M.Integer.t} `{C Self} (z : Z) :
      Z + string :=
    if z <? min then
      inr "underflow"
    else if max <? z then
      inr "overflow"
    else
      inl z.

  Global Instance I_u8 : C Integer.U8 := {
    normalize_wrap z := Z.modulo z 2^8;
    min := 0;
    max := 2^8 - 1;
  }.

  Global Instance I_u16 : C Integer.U16 := {
    normalize_wrap z := Z.modulo z 2^16;
    min := 0;
    max := 2^16 - 1;
  }.

  Global Instance I_u32 : C Integer.U32 := {
    normalize_wrap z := Z.modulo z 2^32;
    min := 0;
    max := 2^32 - 1;
  }.

  Global Instance I_u64 : C Integer.U64 := {
    normalize_wrap z := Z.modulo z 2^64;
    min := 0;
    max := 2^64 - 1;
  }.

  Global Instance I_u128 : C Integer.U128 := {
    normalize_wrap z := Z.modulo z 2^128;
    min := 0;
    max := 2^128 - 1;
  }.

  Global Instance I_usize : C Integer.Usize := {
    normalize_wrap z := Z.modulo z 2^64;
    min := 0;
    max := 2^64 - 1;
  }.

  Global Instance I_i8 : C Integer.I8 := {
    normalize_wrap z := Z.modulo (z + 2^7) 2^8 - 2^7;
    min := -2^7;
    max := 2^7 - 1;
  }.

  Global Instance I_i16 : C Integer.I16 := {
    normalize_wrap z := Z.modulo (z + 2^15) 2^16 - 2^15;
    min := -2^15;
    max := 2^15 - 1;
  }.

  Global Instance I_i32 : C Integer.I32 := {
    normalize_wrap z := Z.modulo (z + 2^31) 2^32 - 2^31;
    min := -2^31;
    max := 2^31 - 1;
  }.

  Global Instance I_i64 : C Integer.I64 := {
    normalize_wrap z := Z.modulo (z + 2^63) 2^64 - 2^63;
    min := -2^63;
    max := 2^63 - 1;
  }.

  Global Instance I_i128 : C Integer.I128 := {
    normalize_wrap z := Z.modulo (z + 2^127) 2^128 - 2^127;
    min := -2^127;
    max := 2^127 - 1;
  }.

  Global Instance I_isize : C Integer.Isize := {
    normalize_wrap z := Z.modulo (z + 2^63) 2^64 - 2^63;
    min := -2^63;
    max := 2^63 - 1;
  }.
End Integer.

Module Eq.
  (** Class for values that can be compared with the primitive equality
      operator. *)
  Class C (Self : Set) : Set := {
    eq : Self -> Self -> bool;
  }.

  Global Instance I_Integer {Self : Set} `{Integer.C Self} : C Self := {
    eq v1 v2 := Z.eqb (Integer.to_Z v1) (Integer.to_Z v2);
  }.

  Global Instance I_char : C char.t := {
    eq := Coq.Strings.Ascii.eqb;
  }.

  Global Instance I_f32 : C f32.t := {
    eq := axiom "eq_f32";
  }.

  Global Instance I_f64 : C f64.t := {
    eq := axiom "eq_f64";
  }.
End Eq.

Module UnOp.
  Module Not.
    Class C (Self : Set) : Set := {
      not : Self -> Self;
    }.

    Global Instance I_bool : C bool.t := {
      not := negb;
    }.

    Global Instance I_u8 : C u8.t := {
      not := axiom "not_u8";
    }.

    (* @TODO: add definitions/axioms for the other integer types *)
  End Not.

  Definition not {A : Set} `{Not.C A} : A -> A :=
    Not.not.

  Parameter neg : forall {A : Set}, A -> M A.
End UnOp.

Module BinOp.
  Module Pure.
    Parameter bit_xor : forall {A : Set}, A -> A -> A.
    Parameter bit_and : forall {A : Set}, A -> A -> A.
    Parameter bit_or : forall {A : Set}, A -> A -> A.

    Definition eq {A : Set} `{Eq.C A} : A -> A -> bool.t :=
      Eq.eq.

    Definition ne {A : Set} `{Eq.C A} : A -> A -> bool.t :=
      fun v1 v2 => negb (eq v1 v2).

    Module Lt.
      Class C (Self : Set) : Set := {
        lt : Self -> Self -> bool.t;
      }.

      Global Instance I_Integer {Self : Set} `{Integer.C Self} : C Self := {
        lt v1 v2 := Z.ltb (Integer.to_Z v1) (Integer.to_Z v2);
      }.

      Global Instance I_f32 : C f32.t := {
        lt := axiom "lt_f32";
      }.

      Global Instance I_f64 : C f64.t := {
        lt := axiom "lt_f64";
      }.
    End Lt.

    Definition lt {A : Set} `{Lt.C A} : A -> A -> bool.t :=
      Lt.lt.

    Module Le.
      Class C (Self : Set) : Set := {
        le : Self -> Self -> bool.t;
      }.

      Global Instance I_Integer {Self : Set} `{Integer.C Self} : C Self := {
        le v1 v2 := Z.leb (Integer.to_Z v1) (Integer.to_Z v2);
      }.

      Global Instance I_f32 : C f32.t := {
        le := axiom "le_f32";
      }.

      Global Instance I_f64 : C f64.t := {
        le := axiom "le_f64";
      }.
    End Le.

    Definition le {A : Set} `{Le.C A} : A -> A -> bool.t :=
      Le.le.

    Module Ge.
      Class C (Self : Set) : Set := {
        ge : Self -> Self -> bool.t;
      }.

      Global Instance I_Integer {Self : Set} `{Integer.C Self} : C Self := {
        ge v1 v2 := Z.geb (Integer.to_Z v1) (Integer.to_Z v2);
      }.

      Global Instance I_f32 : C f32.t := {
        ge := axiom "ge_f32";
      }.

      Global Instance I_f64 : C f64.t := {
        ge := axiom "ge_f64";
      }.
    End Ge.

    Definition ge {A : Set} `{Ge.C A} : A -> A -> bool.t :=
      Ge.ge.

    Module Gt.
      Class C (Self : Set) : Set := {
        gt : Self -> Self -> bool.t;
      }.

      Global Instance I_Integer {Self : Set} `{Integer.C Self} : C Self := {
        gt v1 v2 := Z.gtb (Integer.to_Z v1) (Integer.to_Z v2);
      }.

      Global Instance I_f32 : C f32.t := {
        gt := axiom "gt_f32";
      }.

      Global Instance I_f64 : C f64.t := {
        gt := axiom "gt_f64";
      }.
    End Gt.

    Definition gt {A : Set} `{Gt.C A} : A -> A -> bool.t :=
      Gt.gt.

    Parameter and : forall {A : Set}, A -> A -> bool.t.
    Parameter or : forall {A : Set}, A -> A -> bool.t.
  End Pure.

  Module Error.
    Definition make_arithmetic {A : Set} `{Integer.C A}
        (bin_op : Z -> Z -> Z)
        (v1 v2 : A) :
        A + string :=
      let z1 := Integer.to_Z v1 in
      let z2 := Integer.to_Z v2 in
      Integer.normalize_error (bin_op z1 z2).

    Definition add {A : Set} `{Integer.C A} (v1 v2 : A) : A + string :=
      make_arithmetic Z.add v1 v2.

    Definition sub {A : Set} `{Integer.C A} (v1 v2 : A) : A + string :=
      make_arithmetic Z.sub v1 v2.

    Definition mul {A : Set} `{Integer.C A} (v1 v2 : A) : A + string :=
      make_arithmetic Z.mul v1 v2.

    Parameter div : forall {A : Set}, A -> A -> A + string.
    Parameter rem : forall {A : Set}, A -> A -> A + string.
    
    Parameter shl : forall {A : Set}, A -> i32.t -> A + string.
    Parameter shr : forall {A : Set}, A -> i32.t -> A + string.
  End Error.

  Module Panic.
    Definition make_arithmetic {A : Set} `{Integer.C A}
        (bin_op : Z -> Z -> Z)
        (v1 v2 : A) :
        M A :=
      match Error.make_arithmetic bin_op v1 v2 with
      | inl v => M.pure v
      | inr err => M.panic err
      end.

    Module Add.
      Class C (Self : Set) : Set := {
        add : Self -> Self -> M Self;
      }.

      Global Instance I_Integer {Self : Set} `{Integer.C Self} : C Self := {
        add := make_arithmetic Z.add;
      }.

      Global Instance I_f32 : C f32.t := {
        add := axiom "add_f32";
      }.

      Global Instance I_f64 : C f64.t := {
        add := axiom "add_f64";
      }.
    End Add.

    Definition add {A : Set} `{Add.C A} : A -> A -> M A :=
      Add.add.

    Module Sub.
      Class C (Self : Set) : Set := {
        sub : Self -> Self -> M Self;
      }.

      Global Instance I_Integer {Self : Set} `{Integer.C Self} : C Self := {
        sub := make_arithmetic Z.sub;
      }.

      Global Instance I_f32 : C f32.t := {
        sub := axiom "sub_f32";
      }.

      Global Instance I_f64 : C f64.t := {
        sub := axiom "sub_f64";
      }.
    End Sub.

    Definition sub {A : Set} `{Sub.C A} : A -> A -> M A :=
      Sub.sub.

    Module Mul.
      Class C (Self : Set) : Set := {
        mul : Self -> Self -> M Self;
      }.

      Global Instance I_Integer {Self : Set} `{Integer.C Self} : C Self := {
        mul := make_arithmetic Z.mul;
      }.

      Global Instance I_f32 : C f32.t := {
        mul := axiom "mul_f32";
      }.

      Global Instance I_f64 : C f64.t := {
        mul := axiom "mul_f64";
      }.
    End Mul.

    Definition mul {A : Set} `{Mul.C A} : A -> A -> M A :=
      Mul.mul.

    Parameter div : forall {A : Set}, A -> A -> M A.
    Parameter rem : forall {A : Set}, A -> A -> M A.
    
    Parameter shl : forall {A : Set}, A -> i32.t -> M A.
    Parameter shr : forall {A : Set}, A -> i32.t -> M A.
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
    
    Parameter shl : forall {A : Set}, A -> i32.t -> A.
    Parameter shr : forall {A : Set}, A -> i32.t -> A.
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
    
    Parameter shl : forall {A : Set}, A -> i32.t -> A.
    Parameter shr : forall {A : Set}, A -> i32.t -> A.
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

Fixpoint repeat_nat {A : Set} (times : nat) (v : A) : list A :=
  match times with
  | Datatypes.O => []
  | Datatypes.S times => v :: repeat_nat times v
  end.

(** The repeat operator to create new arrays, like in `[0; 32]`. *)
Definition repeat {A : Set} (v : A) (times : Z) : list A :=
  repeat_nat (Z.to_nat times) v.

Module Tuple.
  Module Access.
    Definition left {A1 A0 : Set} :=
      Ref.map
        (Big := A1 * A0)
        (fun '(x1, _) => Some x1)
        (fun β '(_, x0) => Some (β, x0)).

    Definition right {A1 A0 : Set} :=
      Ref.map
        (Big := A1 * A0)
        (fun '(_, x0) => Some x0)
        (fun β '(x1, _) => Some (x1, β)).
  End Access.
End Tuple.

(** This function is different from the [M.cast] operator of the monad. This
    function is explicitely called in the Rust AST, and should take two types
    that are actually different but convertible, like different kinds of
    integers. *)
Parameter rust_cast : forall {A B : Set}, A -> B.

(** The special type [dyn], that takes a list of traits as parameter. This type
    is defined as opaque, and operations on it (mainly conversions to and from)
    will be defined separately. *)
Parameter dyn : list (Set -> Set) -> Set.
