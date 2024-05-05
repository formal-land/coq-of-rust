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

Module A.
  Definition tt : M :=
    M.of_value (Value.Tuple []).
End A.

Definition assign (target : A.t) (source : A.t) : M :=
  let* _ := M.write target source in
  let* tt := A.tt in
  M.alloc tt.

(** ** Integer types *)

(** A value with an address of type `ref str`. *)
Definition mk_str (s : string) : M :=
  M.of_value (Value.Pointer (Pointer.Immediate (
    Value.Pointer (Pointer.Immediate (
      Value.String s
    ))
  ))).

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

  Definition normalize_with_error (kind : Integer.t) (z : Z) : Z + string :=
    if z <? min kind then
      inr "underflow"
    else if max kind <? z then
      inr "overflow"
    else
      inl z.
End Integer.

Module UnOp.
  Module Pure.
    Definition not (v : A.t) : M :=
      M.of_value match A.to_value v with
      | Value.Bool b => Value.Bool (negb b)
      | Value.Integer i => Value.Integer (Z.lnot i)
      | _ => Value.Error "unexpected parameter for not"
      end.
  End Pure.

  Module Panic.
    Definition neg (kind : Integer.t) (v : A.t) : M :=
      match A.to_value v with
      | Value.Integer i =>
        if Z.eqb i (Integer.min kind) then
          M.panic "overflow"
        else
          M.of_value (Value.Integer (- i))
      | _ => M.of_value (Value.Error "unexpected parameter for neg")
      end.
  End Panic.
End UnOp.

Module BinOp.
  Module Pure.
    Parameter bit_xor : A.t -> A.t -> M.
    Parameter bit_and : A.t -> A.t -> M.
    Parameter bit_or : A.t -> A.t -> M.

    Definition eq (v1 v2 : A.t) : M :=
      let v1 := A.to_value v1 in
      let v2 := A.to_value v2 in
      M.of_value (Value.Bool (Value.eqb v1 v2)).

    Definition ne (v1 v2 : A.t) : M :=
      let v1 := A.to_value v1 in
      let v2 := A.to_value v2 in
      M.of_value (Value.Bool (negb (Value.eqb v1 v2))).

    Definition lt (v1 v2 : A.t) : M :=
      M.of_value match A.to_value v1, A.to_value v2 with
      | Value.Integer i1, Value.Integer i2 => Value.Bool (Z.ltb i1 i2)
      | _, _ => Value.Error "unexpected parameter for lt"
      end.

    Definition le (v1 v2 : A.t) : M :=
      M.of_value match A.to_value v1, A.to_value v2 with
      | Value.Integer i1, Value.Integer i2 => Value.Bool (Z.leb i1 i2)
      | _, _ => Value.Error "unexpected parameter for le"
      end.

    Definition ge (v1 v2 : A.t) : M :=
      M.of_value match A.to_value v1, A.to_value v2 with
      | Value.Integer i1, Value.Integer i2 => Value.Bool (Z.geb i1 i2)
      | _, _ => Value.Error "unexpected parameter for ge"
      end.

    Definition gt (v1 v2 : A.t) : M :=
      M.of_value match A.to_value v1, A.to_value v2 with
      | Value.Integer i1, Value.Integer i2 => Value.Bool (Z.gtb i1 i2)
      | _, _ => Value.Error "unexpected parameter for gt"
      end.
  End Pure.

  Module Error.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        (kind : Integer.t)
        (v1 v2 : Value.t) :
        Value.t + string :=
      match v1, v2 with
      | Value.Integer z1, Value.Integer z2 =>
        match Integer.normalize_with_error kind (bin_op z1 z2) with
        | inl v => inl (Value.Integer v)
        | inr err => inr err
        end
      | _, _ => inr "expected integers"
      end.

    (* Definition add (kind : Integer.t) (v1 v2 : Value.t) : Value.t + string :=
      make_arithmetic Z.add kind v1 v2.

    Definition sub (kind : Integer.t) (v1 v2 : Value.t) : Value.t + string :=
      make_arithmetic Z.sub kind v1 v2.

    Definition mul (kind : Integer.t) (v1 v2 : Value.t) : Value.t + string :=
      make_arithmetic Z.mul kind v1 v2.

    Parameter div : Integer.t -> Value.t -> Value.t -> Value.t + string.
    Parameter rem : Integer.t -> Value.t -> Value.t -> Value.t + string.
    
    Parameter shl : Value.t -> Value.t -> Value.t + string.
    Parameter shr : Value.t -> Value.t -> Value.t + string. *)
  End Error.

  Module Panic.
    Definition make_arithmetic (bin_op : Z -> Z -> Z) (kind : Integer.t) (v1 v2 : A.t) : M :=
      match Error.make_arithmetic bin_op kind (A.to_value v1) (A.to_value v2) with
      | inl v => M.of_value v
      | inr err => M.panic err
      end.

    Definition add (kind : Integer.t) : A.t -> A.t -> M :=
      make_arithmetic Z.add kind.

    Definition sub (kind : Integer.t) : A.t -> A.t -> M :=
      make_arithmetic Z.sub kind.

    Definition mul (kind : Integer.t) : A.t -> A.t -> M :=
      make_arithmetic Z.mul kind.

    Parameter div : Integer.t -> A.t -> A.t -> M.
    Parameter rem : Integer.t -> A.t -> A.t -> M.
    
    Parameter shl : A.t -> A.t -> M.
    Parameter shr : A.t -> A.t -> M.
  End Panic.

  Module Wrap.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        (kind : Integer.t)
        (v1 v2 : A.t) :
        M :=
      M.of_value match A.to_value v1, A.to_value v2 with
      | Value.Integer v1, Value.Integer v2 =>
        let z := Integer.normalize_wrap kind (bin_op v1 v2) in
        Value.Integer z
      | _, _ => Value.Error "expected integers"
      end.

    Definition add (kind : Integer.t) (v1 v2 : A.t) : M :=
      make_arithmetic Z.add kind v1 v2.

    Definition sub (kind : Integer.t) (v1 v2 : A.t) : M :=
      make_arithmetic Z.sub kind v1 v2.

    Definition mul (kind : Integer.t) (v1 v2 : A.t) : M :=
      make_arithmetic Z.mul kind v1 v2.

    Parameter div : Integer.t -> A.t -> A.t -> M.
    Parameter rem : Integer.t -> A.t -> A.t -> M.

    Parameter shl : A.t -> A.t -> M.
    Parameter shr : A.t -> A.t -> M.
  End Wrap.

  Module Optimistic.
    (** We assume that the operation will not overflow, and we do not check
        for it. This is the optimistic approach. These operators can be used
        in the simulations when possible, to simplify the proofs. *)
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        (v1 v2 : A.t) :
        M :=
      M.of_value match A.to_value v1, A.to_value v2 with
      | Value.Integer v1, Value.Integer v2 =>
        let z := bin_op v1 v2 in
        Value.Integer z
      | _, _ => Value.Error "expected integers"
      end.

    Definition add (v1 v2 : A.t) : M :=
      make_arithmetic Z.add v1 v2.

    Definition sub (v1 v2 : A.t) : M :=
      make_arithmetic Z.sub v1 v2.

    Definition mul (v1 v2 : A.t) : M :=
      make_arithmetic Z.mul v1 v2.

    Parameter div : A.t -> A.t -> M.
    Parameter rem : A.t -> A.t -> M.

    Parameter shl : A.t -> A.t -> M.
    Parameter shr : A.t -> A.t -> M.
  End Optimistic.
End BinOp.

(** The evaluation of logical operators is lazy on the second parameter. *)
Module LogicalOp.
  Definition and (lhs : A.t) (rhs : M) : M :=
    match A.to_value lhs with
    | Value.Bool b =>
      if b then
        rhs
      else
        M.of_value (Value.Bool false)
    | _ => M.impossible
    end.

  Definition or (lhs : A.t) (rhs : M) : M :=
    match A.to_value lhs with
    | Value.Bool b =>
      if b then
        M.of_value (Value.Bool true)
      else
        rhs
    | _ => M.impossible
    end.
End LogicalOp.

Fixpoint repeat_nat {A : Set} (times : nat) (v : A) : list A :=
  match times with
  | Datatypes.O => []
  | Datatypes.S times => v :: repeat_nat times v
  end.

(** The repeat operator to create new arrays, like in `[0; 32]`. *)
Definition repeat (v : A.t) (times : Z) : M :=
  M.of_value (Value.Array (repeat_nat (Z.to_nat times) (A.to_value v))).
