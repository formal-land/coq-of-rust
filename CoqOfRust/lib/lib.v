Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.String.
Require Export Coq.ZArith.ZArith.
Require Export CoqOfRust.RecordUpdate.

(* Global settings for files importing this file *)
Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope string_scope.
Global Open Scope list_scope.
Global Open Scope Z_scope.
Global Open Scope type_scope.
Global Open Scope bool_scope.

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

Module Ty.
  Parameter path : string -> Ty.t.

  Parameter apply : Ty.t -> list Value.t -> list Ty.t -> Ty.t.

  Parameter function : list Ty.t -> Ty.t -> Ty.t.

  Parameter tuple : list Ty.t -> Ty.t.

  (** As parameter: a list of traits, described by their absolute name and their
      list of type parameters, excluding `Self`. *)
  Parameter dyn : list (string * list Ty.t) -> Ty.t.

  (** This primitive is for associated types; it will require additional
      parameters. *)
  Parameter associated : Ty.t.
End Ty.

Definition assign (target : Value.t) (source : Value.t) : M :=
  let* _ := M.write target source in
  M.alloc (Value.Tuple []).

(** ** Integer types *)

(** A value with an address of type `ref str`. *)
Definition mk_str (s : string) : M :=
  let* pointer := M.alloc (Value.String s) in
  M.alloc pointer.

Module Integer.
  Definition min (kind : IntegerKind.t) : Z :=
    match kind with
    | IntegerKind.U8 => 0
    | IntegerKind.U16 => 0
    | IntegerKind.U32 => 0
    | IntegerKind.U64 => 0
    | IntegerKind.U128 => 0
    | IntegerKind.Usize => 0
    | IntegerKind.I8 => -2^7
    | IntegerKind.I16 => -2^15
    | IntegerKind.I32 => -2^31
    | IntegerKind.I64 => -2^63
    | IntegerKind.I128 => -2^127
    | IntegerKind.Isize => -2^63
    end.
  Global Hint Unfold min : coq_of_rust_z.

  Definition max (kind : IntegerKind.t) : Z :=
    match kind with
    | IntegerKind.U8 => 2^8 - 1
    | IntegerKind.U16 => 2^16 - 1
    | IntegerKind.U32 => 2^32 - 1
    | IntegerKind.U64 => 2^64 - 1
    | IntegerKind.U128 => 2^128 - 1
    | IntegerKind.Usize => 2^64 - 1
    | IntegerKind.I8 => 2^7 - 1
    | IntegerKind.I16 => 2^15 - 1
    | IntegerKind.I32 => 2^31 - 1
    | IntegerKind.I64 => 2^63 - 1
    | IntegerKind.I128 => 2^127 - 1
    | IntegerKind.Isize => 2^63 - 1
    end.
  Global Hint Unfold max : coq_of_rust_z.

  Definition normalize_wrap (kind : IntegerKind.t) (z : Z) : Z :=
    match kind with
    | IntegerKind.U8 => Z.modulo z (2^8)
    | IntegerKind.U16 => Z.modulo z (2^16)
    | IntegerKind.U32 => Z.modulo z (2^32)
    | IntegerKind.U64 => Z.modulo z (2^64)
    | IntegerKind.U128 => Z.modulo z (2^128)
    | IntegerKind.Usize => Z.modulo z (2^64)
    | IntegerKind.I8 => Z.modulo (z + 2^7) (2^8) - 2^7
    | IntegerKind.I16 => Z.modulo (z + 2^15) (2^16) - 2^15
    | IntegerKind.I32 => Z.modulo (z + 2^31) (2^32) - 2^31
    | IntegerKind.I64 => Z.modulo (z + 2^63) (2^64) - 2^63
    | IntegerKind.I128 => Z.modulo (z + 2^127) (2^128) - 2^127
    | IntegerKind.Isize => Z.modulo (z + 2^63) (2^64) - 2^63
    end.

  Definition normalize_option (kind : IntegerKind.t) (z : Z) : option Z :=
    if z <? min kind then
      None
    else if max kind <? z then
      None
    else
      Some z.
End Integer.

(** We define the operators for the release mode. That means that we make overflows on integers
    instead of a panic in debug mode. *)

Module UnOp.
  Definition not (v : Value.t) : M :=
    match v with
    | Value.Bool b => M.pure (Value.Bool (negb b))
    | Value.Integer kind i => M.pure (Value.Integer kind (Z.lnot i))
    | _ => M.impossible "unexpected parameter for not"
    end.

  Definition neg (v : Value.t) : M :=
    match v with
    | Value.Integer kind i =>
      if Z.eqb i (Integer.min kind) then
        M.pure v
      else
        M.pure (Value.Integer kind (- i))
    | _ => M.impossible "unexpected parameter for neg"
    end.
End UnOp.

Module BinOp.
  Parameter bit_xor : Value.t -> Value.t -> Value.t.
  Parameter bit_and : Value.t -> Value.t -> Value.t.
  Parameter bit_or : Value.t -> Value.t -> Value.t.

  Definition eq : Value.t -> Value.t -> M :=
    M.are_equal.

  Definition ne (v1 v2 : Value.t) : M :=
    let* are_equal := M.are_equal v1 v2 in
    match are_equal with
    | Value.Bool are_equal => M.pure (Value.Bool (negb are_equal))
    | _ => M.impossible "expected a boolean for the equality"
    end.

  Definition lt (v1 v2 : Value.t) : M :=
    match v1, v2 with
    | Value.Integer kind1 i1, Value.Integer kind2 i2 =>
      M.pure (Value.Bool (andb (IntegerKind.eqb kind1 kind2) (Z.ltb i1 i2)))
    | _, _ => M.impossible "unexpected parameter for lt"
    end.

  Definition le (v1 v2 : Value.t) : M :=
    match v1, v2 with
    | Value.Integer kind1 i1, Value.Integer kind2 i2 =>
      M.pure (Value.Bool (andb (IntegerKind.eqb kind1 kind2) (Z.leb i1 i2)))
    | _, _ => M.impossible "unexpected parameter for le"
    end.

  Definition ge (v1 v2 : Value.t) : M :=
    match v1, v2 with
    | Value.Integer kind1 i1, Value.Integer kind2 i2 =>
      M.pure (Value.Bool (andb (IntegerKind.eqb kind1 kind2) (Z.geb i1 i2)))
    | _, _ => M.impossible "unexpected parameter for ge"
    end.

  Definition gt (v1 v2 : Value.t) : M :=
    match v1, v2 with
    | Value.Integer kind1 i1, Value.Integer kind2 i2 =>
      M.pure (Value.Bool (andb (IntegerKind.eqb kind1 kind2) (Z.gtb i1 i2)))
    | _, _ => M.impossible "unexpected parameter for gt"
    end.

  Module Wrap.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        (v1 v2 : Value.t) :
        M :=
      match v1, v2 with
      | Value.Integer kind1 v1, Value.Integer kind2 v2 =>
        if negb (IntegerKind.eqb kind1 kind2) then
          M.impossible "expected the same kind of integers"
        else
          let z := Integer.normalize_wrap kind1 (bin_op v1 v2) in
          M.pure (Value.Integer kind1 z)
      | _, _ => M.impossible "expected integers"
      end.

    Definition add (v1 v2 : Value.t) : M :=
      make_arithmetic Z.add v1 v2.

    Definition sub (v1 v2 : Value.t) : M :=
      make_arithmetic Z.sub v1 v2.

    Definition mul (v1 v2 : Value.t) : M :=
      make_arithmetic Z.mul v1 v2.

    Definition div (v1 v2 : Value.t) : M :=
      make_arithmetic Z.div v1 v2.

    Definition rem (v1 v2 : Value.t) : M :=
      make_arithmetic Z.modulo v1 v2.

    Parameter shl : Value.t -> Value.t -> M.
    Parameter shr : Value.t -> Value.t -> M.
  End Wrap.
End BinOp.

(** The evaluation of logical operators is lazy on the second parameter. *)
Module LogicalOp.
  Definition and (lhs : Value.t) (rhs : M) : M :=
    match lhs with
    | Value.Bool b =>
      if b then
        rhs
      else
        M.pure (Value.Bool false)
    | _ => M.impossible "expected a boolean"
    end.

  Definition or (lhs : Value.t) (rhs : M) : M :=
    match lhs with
    | Value.Bool b =>
      if b then
        M.pure (Value.Bool true)
      else
        rhs
    | _ => M.impossible "expected a boolean"
    end.
End LogicalOp.

Fixpoint repeat_nat {A : Set} (times : nat) (v : A) : list A :=
  match times with
  | Datatypes.O => []
  | Datatypes.S times => v :: repeat_nat times v
  end.

(** The repeat operator to create new arrays, like in `[0; 32]`. *)
Definition repeat (v times : Value.t) : M :=
  match times with
  | Value.Integer IntegerKind.Usize times => M.pure (Value.Array (repeat_nat (Z.to_nat times) v))
  | _ => M.impossible "expected a usize integer for the repeat operator"
  end.

(** There is an automatic instanciation of the function traits for closures and functions. *)
Module FunctionTraitAutomaticImpl.
  Axiom FunctionImplementsFn :
    forall (Args : list Ty.t) (Output : Ty.t),
    M.IsTraitInstance
      "core::ops::function::Fn"
      (Ty.function Args Output)
      (* Trait polymorphic types *) [Ty.tuple Args]
      (* Instance *) [ ("call", InstanceField.Method (fun ε τ α =>
        match ε, τ, α with
        | [], [], [self; Value.Tuple args] =>
          let* self := M.read self in
          M.call_closure self args
        | _, _, _ => M.impossible "wrong number of arguments"
        end
      )) ].

  Axiom FunctionImplementsFnMut :
    forall (Args : list Ty.t) (Output : Ty.t),
    M.IsTraitInstance
      "core::ops::function::FnMut"
      (Ty.function Args Output)
      (* Trait polymorphic types *) [Ty.tuple Args]
      (* Instance *) [ ("call_mut", InstanceField.Method (fun ε τ α =>
        match ε, τ, α with
        | [], [], [self; Value.Tuple args] =>
          let* self := M.read self in
          M.call_closure self args
        | _, _, _ => M.impossible "wrong number of arguments"
        end
      )) ].

  Axiom FunctionImplementsFnOnce :
    forall (Args : list Ty.t) (Output : Ty.t),
    M.IsTraitInstance
      "core::ops::function::FnOnce"
      (Ty.function Args Output)
      (* Trait polymorphic types *) [Ty.tuple Args]
      (* Instance *) [ ("call_once", InstanceField.Method (fun ε τ α =>
        match ε, τ, α with
        | [], [], [self; Value.Tuple args] =>
          M.call_closure self args
        | _, _, _ => M.impossible "wrong number of arguments"
        end
      )) ].
End FunctionTraitAutomaticImpl.
