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

Module List.
  (** Check the equality of two lists. *)
  Fixpoint eqb {A : Set} (item_eqb : A -> A -> bool ) (l1 l2 : list A) : bool :=
    match l1, l2 with
    | [], [] => true
    | x1 :: l1, x2 :: l2 => andb (eqb item_eqb l1 l2) (item_eqb x1 x2)
    | _, _ => false
    end.
End List.

Notation "ty ::[ name ]" := (M.associated_function ty name)
  (at level 0).

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
  Definition min (kind : Integer.t) : Z :=
    match kind with
    | Integer.U8 => 0
    | Integer.U16 => 0
    | Integer.U32 => 0
    | Integer.U64 => 0
    | Integer.U128 => 0
    | Integer.Usize => 0
    | Integer.I8 => -2^7
    | Integer.I16 => -2^15
    | Integer.I32 => -2^31
    | Integer.I64 => -2^63
    | Integer.I128 => -2^127
    | Integer.Isize => -2^63
    end.

  Definition max (kind : Integer.t) : Z :=
    match kind with
    | Integer.U8 => 2^8 - 1
    | Integer.U16 => 2^16 - 1
    | Integer.U32 => 2^32 - 1
    | Integer.U64 => 2^64 - 1
    | Integer.U128 => 2^128 - 1
    | Integer.Usize => 2^64 - 1
    | Integer.I8 => 2^7 - 1
    | Integer.I16 => 2^15 - 1
    | Integer.I32 => 2^31 - 1
    | Integer.I64 => 2^63 - 1
    | Integer.I128 => 2^127 - 1
    | Integer.Isize => 2^63 - 1
    end.

  Definition normalize_wrap (kind : Integer.t) (z : Z) : Z :=
    match kind with
    | Integer.U8 => Z.modulo z 2^8
    | Integer.U16 => Z.modulo z 2^16
    | Integer.U32 => Z.modulo z 2^32
    | Integer.U64 => Z.modulo z 2^64
    | Integer.U128 => Z.modulo z 2^128
    | Integer.Usize => Z.modulo z 2^64
    | Integer.I8 => Z.modulo (z + 2^7) 2^8 - 2^7
    | Integer.I16 => Z.modulo (z + 2^15) 2^16 - 2^15
    | Integer.I32 => Z.modulo (z + 2^31) 2^32 - 2^31
    | Integer.I64 => Z.modulo (z + 2^63) 2^64 - 2^63
    | Integer.I128 => Z.modulo (z + 2^127) 2^128 - 2^127
    | Integer.Isize => Z.modulo (z + 2^63) 2^64 - 2^63
    end.

  Definition normalize_with_error (kind : Integer.t) (z : Z) :
      Value.t + string :=
    if z <? min kind then
      inr "underflow"
    else if max kind <? z then
      inr "overflow"
    else
      inl (Value.Integer kind z).
End Integer.

Module Eq.
  (** Equality between values. Defined only for basic types. *)
  Definition eqb (v1 v2 : Value.t) : bool :=
    match v1, v2 with
    | Value.Bool b1, Value.Bool b2 => Bool.eqb b1 b2
    | Value.Integer _ i1, Value.Integer _ i2 => Z.eqb i1 i2
    | Value.Float f1, Value.Float f2 => String.eqb f1 f2
    | Value.UnicodeChar c1, Value.UnicodeChar c2 => Z.eqb c1 c2
    | Value.String s1, Value.String s2 => String.eqb s1 s2
    | Value.Tuple _, Value.Tuple _
      | Value.Array _, Value.Array _
      | Value.StructRecord _ _, Value.StructRecord _ _
      | Value.StructTuple _ _, Value.StructTuple _ _
      | Value.Pointer _, Value.Pointer _
      | Value.Closure _, Value.Closure _
      | Value.Error _, Value.Error _
      | Value.DeclaredButUndefined, Value.DeclaredButUndefined =>
      true
    | _, _ => false
    end.

    Lemma eqb_is_reflexive (v : Value.t) : eqb v v = true.
    Proof.
      destruct v; simpl;
        try reflexivity;
        try apply Z.eqb_refl;
        try apply String.eqb_refl.
      now destruct_all bool.
    Qed.
End Eq.

Module UnOp.
  Module Pure.
    Definition not (v : Value.t) : Value.t :=
      match v with
      | Value.Bool b => Value.Bool (negb b)
      | Value.Integer kind i => Value.Integer kind (Z.lnot i)
      | _ => v
      end.
  End Pure.

  Module Panic.
    Definition neg (v : Value.t) : M :=
      match v with
      | Value.Integer kind i =>
        if Z.eqb i (Integer.min kind) then
          M.panic "overflow"
        else
          M.pure (Value.Integer kind (- i))
      | _ => M.panic "not implemented"
      end.
  End Panic.
End UnOp.

Module BinOp.
  Module Pure.
    Parameter bit_xor : Value.t -> Value.t -> Value.t.
    Parameter bit_and : Value.t -> Value.t -> Value.t.
    Parameter bit_or : Value.t -> Value.t -> Value.t.

    Definition eq (v1 v2 : Value.t) : Value.t :=
      Value.Bool (Eq.eqb v1 v2).

    Definition ne (v1 v2 : Value.t) : Value.t :=
      Value.Bool (negb (Eq.eqb v1 v2)).

    Definition lt (v1 v2 : Value.t) : Value.t :=
      match v1, v2 with
      | Value.Integer _ i1, Value.Integer _ i2 => Value.Bool (Z.ltb i1 i2)
      | _, _ => Value.Bool false
      end.

    Definition le (v1 v2 : Value.t) : Value.t :=
      match v1, v2 with
      | Value.Integer _ i1, Value.Integer _ i2 => Value.Bool (Z.leb i1 i2)
      | _, _ => Value.Bool true
      end.

    Definition ge (v1 v2 : Value.t) : Value.t :=
      match v1, v2 with
      | Value.Integer _ i1, Value.Integer _ i2 => Value.Bool (Z.geb i1 i2)
      | _, _ => Value.Bool true
      end.

    Definition gt (v1 v2 : Value.t) : Value.t :=
      match v1, v2 with
      | Value.Integer _ i1, Value.Integer _ i2 => Value.Bool (Z.gtb i1 i2)
      | _, _ => Value.Bool false
      end.

    Parameter and : Value.t -> Value.t -> Value.t.
    Parameter or : Value.t -> Value.t -> Value.t.
  End Pure.

  Module Error.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        (v1 v2 : Value.t) :
        Value.t + string :=
      match v1, v2 with
      | Value.Integer kind z1, Value.Integer _ z2 =>
        Integer.normalize_with_error kind (bin_op z1 z2)
      | _, _ => inr "expected integers"
      end.

    Definition add (v1 v2 : Value.t) : Value.t + string :=
      make_arithmetic Z.add v1 v2.

    Definition sub (v1 v2 : Value.t) : Value.t + string :=
      make_arithmetic Z.sub v1 v2.

    Definition mul (v1 v2 : Value.t) : Value.t + string :=
      make_arithmetic Z.mul v1 v2.

    Parameter div :  Value.t -> Value.t -> Value.t + string.
    Parameter rem :  Value.t -> Value.t -> Value.t + string.
    
    Parameter shl : Value.t -> Value.t -> Value.t + string.
    Parameter shr : Value.t -> Value.t -> Value.t + string.
  End Error.

  Module Panic.
    Definition make_arithmetic (bin_op : Z -> Z -> Z) (v1 v2 : Value.t) : M :=
      match Error.make_arithmetic bin_op v1 v2 with
      | inl v => M.pure v
      | inr err => M.panic err
      end.

    Definition add : Value.t -> Value.t -> M :=
      make_arithmetic Z.add.

    Definition sub : Value.t -> Value.t -> M :=
      make_arithmetic Z.sub.

    Definition mul : Value.t -> Value.t -> M :=
      make_arithmetic Z.mul.

    Parameter div : Value.t -> Value.t -> M.
    Parameter rem : Value.t -> Value.t -> M.
    
    Parameter shl : Value.t -> Value.t -> M.
    Parameter shr : Value.t -> Value.t -> M.
  End Panic.

  Module Wrap.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        (v1 v2 : Value.t) :
        Value.t :=
      match v1, v2 with
      | Value.Integer kind v1, Value.Integer _ v2 =>
        let z := Integer.normalize_wrap kind (bin_op v1 v2) in
        Value.Integer kind z
      | _, _ => Value.Error "expected integers"
      end.

    Definition add (v1 v2 : Value.t) : Value.t :=
      make_arithmetic Z.add v1 v2.

    Definition sub (v1 v2 : Value.t) : Value.t :=
      make_arithmetic Z.sub v1 v2.

    Definition mul (v1 v2 : Value.t) : Value.t :=
      make_arithmetic Z.mul v1 v2.

    Parameter div : Value.t -> Value.t -> Value.t.
    Parameter rem : Value.t -> Value.t -> Value.t.
    
    Parameter shl : Value.t -> Value.t -> Value.t.
    Parameter shr : Value.t -> Value.t -> Value.t.
  End Wrap.

  Module Optimistic.
    (** We assume that the operation will not overflow, and we do not check
        for it. This is the optimistic approach. These operators can be used
        in the simulations when possible, to simplify the proofs. *)
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        (v1 v2 : Value.t) :
        Value.t :=
      match v1, v2 with
      | Value.Integer kind v1, Value.Integer _ v2 =>
        let z := bin_op v1 v2 in
        Value.Integer kind z
      | _, _ => Value.Error "expected integers"
      end.

    Definition add (v1 v2 : Value.t) : Value.t :=
      make_arithmetic Z.add v1 v2.

    Definition sub (v1 v2 : Value.t) : Value.t :=
      make_arithmetic Z.sub v1 v2.

    Definition mul (v1 v2 : Value.t) : Value.t :=
      make_arithmetic Z.mul v1 v2.

    Parameter div : Value.t -> Value.t -> Value.t.
    Parameter rem : Value.t -> Value.t -> Value.t.
    
    Parameter shl : Value.t -> Value.t -> Value.t.
    Parameter shr : Value.t -> Value.t -> Value.t.
  End Optimistic.
End BinOp.

(** ** Integer notations *)

Infix "==u8" := BinOp.Pure.eq (at level 60).
Infix "!=u8" := BinOp.Pure.ne (at level 60).
Infix "<u8"  := BinOp.Pure.lt (at level 60).
Infix "<=u8" := BinOp.Pure.le (at level 60).
Infix ">=u8" := BinOp.Pure.ge (at level 60).
Infix ">u8"  := BinOp.Pure.gt (at level 60).

Infix "==u16" := BinOp.Pure.eq (at level 60).
Infix "!=u16" := BinOp.Pure.ne (at level 60).
Infix "<u16"  := BinOp.Pure.lt (at level 60).
Infix "<=u16" := BinOp.Pure.le (at level 60).
Infix ">=u16" := BinOp.Pure.ge (at level 60).
Infix ">u16"  := BinOp.Pure.gt (at level 60).

Infix "==u32" := BinOp.Pure.eq (at level 60).
Infix "!=u32" := BinOp.Pure.ne (at level 60).
Infix "<u32"  := BinOp.Pure.lt (at level 60).
Infix "<=u32" := BinOp.Pure.le (at level 60).
Infix ">=u32" := BinOp.Pure.ge (at level 60).
Infix ">u32"  := BinOp.Pure.gt (at level 60).

Infix "==u64" := BinOp.Pure.eq (at level 60).
Infix "!=u64" := BinOp.Pure.ne (at level 60).
Infix "<u64"  := BinOp.Pure.lt (at level 60).
Infix "<=u64" := BinOp.Pure.le (at level 60).
Infix ">=u64" := BinOp.Pure.ge (at level 60).
Infix ">u64"  := BinOp.Pure.gt (at level 60).

Infix "==u128" := BinOp.Pure.eq (at level 60).
Infix "!=u128" := BinOp.Pure.ne (at level 60).
Infix "<u128"  := BinOp.Pure.lt (at level 60).
Infix "<=u128" := BinOp.Pure.le (at level 60).
Infix ">=u128" := BinOp.Pure.ge (at level 60).
Infix ">u128"  := BinOp.Pure.gt (at level 60).

Infix "==usize" := BinOp.Pure.eq (at level 60).
Infix "!=usize" := BinOp.Pure.ne (at level 60).
Infix "<usize"  := BinOp.Pure.lt (at level 60).
Infix "<=usize" := BinOp.Pure.le (at level 60).
Infix ">=usize" := BinOp.Pure.ge (at level 60).
Infix ">usize"  := BinOp.Pure.gt (at level 60).

Infix "==i8" := BinOp.Pure.eq (at level 60).
Infix "!=i8" := BinOp.Pure.ne (at level 60).
Infix "<i8"  := BinOp.Pure.lt (at level 60).
Infix "<=i8" := BinOp.Pure.le (at level 60).
Infix ">=i8" := BinOp.Pure.ge (at level 60).
Infix ">i8"  := BinOp.Pure.gt (at level 60).

Infix "==i16" := BinOp.Pure.eq (at level 60).
Infix "!=i16" := BinOp.Pure.ne (at level 60).
Infix "<i16"  := BinOp.Pure.lt (at level 60).
Infix "<=i16" := BinOp.Pure.le (at level 60).
Infix ">=i16" := BinOp.Pure.ge (at level 60).
Infix ">i16"  := BinOp.Pure.gt (at level 60).

Infix "==i32" := BinOp.Pure.eq (at level 60).
Infix "!=i32" := BinOp.Pure.ne (at level 60).
Infix "<i32"  := BinOp.Pure.lt (at level 60).
Infix "<=i32" := BinOp.Pure.le (at level 60).
Infix ">=i32" := BinOp.Pure.ge (at level 60).
Infix ">i32"  := BinOp.Pure.gt (at level 60).

Infix "==i64" := BinOp.Pure.eq (at level 60).
Infix "!=i64" := BinOp.Pure.ne (at level 60).
Infix "<i64"  := BinOp.Pure.lt (at level 60).
Infix "<=i64" := BinOp.Pure.le (at level 60).
Infix ">=i64" := BinOp.Pure.ge (at level 60).
Infix ">i64"  := BinOp.Pure.gt (at level 60).

Infix "==i128" := BinOp.Pure.eq (at level 60).
Infix "!=i128" := BinOp.Pure.ne (at level 60).
Infix "<i128"  := BinOp.Pure.lt (at level 60).
Infix "<=i128" := BinOp.Pure.le (at level 60).
Infix ">=i128" := BinOp.Pure.ge (at level 60).
Infix ">i128"  := BinOp.Pure.gt (at level 60).

Infix "==isize" := BinOp.Pure.eq (at level 60).
Infix "!=isize" := BinOp.Pure.ne (at level 60).
Infix "<isize"  := BinOp.Pure.lt (at level 60).
Infix "<=isize" := BinOp.Pure.le (at level 60).
Infix ">=isize" := BinOp.Pure.ge (at level 60).
Infix ">isize"  := BinOp.Pure.gt (at level 60).

Fixpoint repeat_nat {A : Set} (times : nat) (v : A) : list A :=
  match times with
  | Datatypes.O => []
  | Datatypes.S times => v :: repeat_nat times v
  end.

(** The repeat operator to create new arrays, like in `[0; 32]`. *)
Definition repeat (v : Value.t) (times : Z) : Value.t :=
  Value.Array (repeat_nat (Z.to_nat times) v).

(** This function is different from the [M.cast] operator of the monad. This
    function is explicitely called in the Rust AST, and should take two types
    that are actually different but convertible, like different kinds of
    integers. *)
Parameter rust_cast : Value.t -> Value.t.
