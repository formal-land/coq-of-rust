Require Export Coq.Numbers.Cyclic.Int63.PrimInt63.
Require Export Coq.Strings.Ascii.
Require Export Coq.Strings.PrimString.
Require Export Coq.ZArith.ZArith.
Require Export CoqOfRust.RecordUpdate.

(* Global settings for files importing this file *)
Global Set Primitive Projections.
Global Set Printing Projections.
Global Open Scope pstring_scope.
Global Open Scope Z_scope.
Global Open Scope list_scope.
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
  Parameter apply : Ty.t -> list Value.t -> list Ty.t -> Ty.t.

  (** As parameter: a list of traits, described by their absolute name and their
      list of type parameters, excluding `Self`. *)
  Parameter dyn : list (string * list Ty.t) -> Ty.t.

  Parameter associated_in_trait : string -> list Value.t -> list Ty.t -> Ty.t -> string -> Ty.t.

  (** This primitive is for associated types that we do not handle (yet). *)
  Parameter associated_unknown : Ty.t.
End Ty.

Definition assign (target : Value.t) (source : Value.t) : M :=
  let* _ := M.write target source in
  M.alloc (Ty.tuple []) (Value.Tuple []).

Definition get_constant (name : string) (return_ty : Ty.t) : M :=
  let* constant := call_primitive (Primitive.GetFunction name [] []) in
  call_closure (Ty.apply (Ty.path "*") [] [return_ty]) constant [].

Definition get_associated_constant (ty : Ty.t) (name : string) (return_ty : Ty.t) : M :=
  let* constant := call_primitive (Primitive.GetAssociatedFunction ty name [] []) in
  call_closure (Ty.apply (Ty.path "*") [] [return_ty]) constant [].

(** ** Integer types *)

(** A value with an address of type `ref str`. *)
Definition mk_str (s : string) : M :=
  let* pointer := M.alloc (Ty.path "str") (Value.String s) in
  M.borrow Pointer.Kind.Ref pointer.

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
  Definition not : Value.t :=
    M.closure (fun args =>
      match args with
      | [Value.Bool b] => M.pure (Value.Bool (negb b))
      | [Value.Integer kind i] => M.pure (Value.Integer kind (Z.lnot i))
      | _ => M.impossible "unexpected parameter for not"
      end
    ).

  Definition neg : Value.t :=
    M.closure (fun args =>
      match args with
      | [Value.Integer kind i] =>
        M.pure (Value.Integer kind (
          if Z.eqb i (Integer.min kind) then
             i
          else
            - i
        ))
      | _ => M.impossible "unexpected parameters for neg"
      end
    ).
End UnOp.

Module BinOp.
  Definition eq : Value.t :=
    M.closure (fun args =>
      match args with
      | [value1; value2] =>
        match value1, value2 with
        | Value.Bool b1, Value.Bool b2 =>
          M.pure (Value.Bool (Bool.eqb b1 b2))
        | Value.Integer kind1 i1, Value.Integer kind2 i2 =>
          if negb (IntegerKind.eqb kind1 kind2) then
            M.impossible "expected the same kind of integers"
          else
            M.pure (Value.Bool (Z.eqb i1 i2))
        | _, _ => M.impossible "expected two values for eq"
        end
      | _ => M.impossible "expected two values for eq"
      end
    ).

  Definition ne : Value.t :=
    M.closure (fun args =>
      match args with
      | [value1; value2] =>
        match args with
        | [value1; value2] =>
          match value1, value2 with
          | Value.Bool b1, Value.Bool b2 =>
            M.pure (Value.Bool (negb (Bool.eqb b1 b2)))
          | Value.Integer kind1 i1, Value.Integer kind2 i2 =>
            if negb (IntegerKind.eqb kind1 kind2) then
              M.impossible "expected the same kind of integers"
            else
              M.pure (Value.Bool (negb (Z.eqb i1 i2)))
          | _, _ => M.impossible "expected two values for ne"
          end
        | _ => M.impossible "expected two values for ne"
        end
      | _ => M.impossible "expected two values for ne"
      end
    ).
  Definition make_Z_comparison (cmp : Z -> Z -> bool) : Value.t :=
    M.closure (fun args =>
      match args with
      | [Value.Integer kind1 i1; Value.Integer kind2 i2] =>
        if negb (IntegerKind.eqb kind1 kind2) then
          M.impossible "expected the same kind of integers"
        else
          M.pure (Value.Bool (cmp i1 i2))
      | _ => M.impossible "expected two integers for comparison"
      end
    ).

  Definition lt : Value.t :=
    make_Z_comparison Z.ltb.

  Definition le : Value.t :=
    make_Z_comparison Z.leb.

  Definition gt : Value.t :=
    make_Z_comparison Z.gtb.

  Definition ge : Value.t :=
    make_Z_comparison Z.geb.

  Module Wrap.
    Definition make_arithmetic
        (bin_op : Z -> Z -> Z)
        : Value.t :=
      M.closure (fun args =>
        match args with
        | [Value.Integer kind1 v1; Value.Integer _ v2] =>
          (* The [kind2] might be different, for example for right/left *)
          let z := Integer.normalize_wrap kind1 (bin_op v1 v2) in
          M.pure (Value.Integer kind1 z)
        | _ => M.impossible "expected two integers for arithmetic"
        end
      ).

    Definition add : Value.t :=
      make_arithmetic Z.add.

    Definition sub : Value.t :=
      make_arithmetic Z.sub.

    Definition mul : Value.t :=
      make_arithmetic Z.mul.

    Definition div : Value.t :=
      make_arithmetic Z.div.

    Definition rem : Value.t :=
      make_arithmetic Z.modulo.

    Definition shl : Value.t :=
      make_arithmetic Z.shiftl.

    Definition shr : Value.t :=
      make_arithmetic Z.shiftr.

    Definition make_bool_or_arithmetic
      (bin_op_bool : bool -> bool -> bool)
      (bin_op_Z : Z -> Z -> Z)
      : Value.t :=
      M.closure (fun args =>
        match args with
        | [Value.Bool b1; Value.Bool b2] => M.pure (Value.Bool (bin_op_bool b1 b2))
        | [Value.Integer kind1 v1; Value.Integer kind2 v2] =>
          if negb (IntegerKind.eqb kind1 kind2) then
            M.impossible "expected the same kind of integers"
          else
            let z := bin_op_Z v1 v2 in
            M.pure (Value.Integer kind1 (Integer.normalize_wrap kind1 z))
        | _ => M.impossible "expected two values for bool or arithmetic"
        end
      ).

    Definition bit_xor : Value.t :=
      make_bool_or_arithmetic xorb Z.lxor.

    Definition bit_and : Value.t :=
      make_bool_or_arithmetic andb Z.land.

    Definition bit_or : Value.t :=
      make_bool_or_arithmetic orb Z.lor.
  End Wrap.
End BinOp.

(** The evaluation of logical operators is lazy on the second parameter. *)
Module LogicalOp.
  Definition and (lhs : Value.t) (rhs : M) : M :=
    M.call_logical_op LogicalOp.And lhs rhs.

  Definition or (lhs : Value.t) (rhs : M) : M :=
    M.call_logical_op LogicalOp.Or lhs rhs.
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

Global Opaque repeat.

Definition is_constant_or_break_match (value expected_value : Value.t) : M :=
  let* are_equal := M.call_closure (Ty.path "bool") BinOp.eq [value; expected_value] in
  if_then_else_bool (Ty.tuple []) are_equal (pure (Value.Tuple [])) break_match.

(** There is an automatic instanciation of the function traits for closures and functions. *)
Module FunctionTraitAutomaticImpl.
  Axiom FunctionImplementsFn :
    forall (Args : list Ty.t) (Output : Ty.t),
    M.IsTraitInstance
      "core::ops::function::Fn"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) [Ty.tuple Args]
      (Ty.function Args Output)
      (* Instance *) [ ("call", InstanceField.Method (fun ε τ α =>
        match ε, τ, α with
        | [], [], [self; Value.Tuple args] =>
          let* self := M.read self in
          M.call_closure Output self args
        | _, _, _ => M.impossible "wrong number of arguments"
        end
      )) ].

  Axiom FunctionImplementsFnMut :
    forall (Args : list Ty.t) (Output : Ty.t),
    M.IsTraitInstance
      "core::ops::function::FnMut"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) [Ty.tuple Args]
      (Ty.function Args Output)
      (* Instance *) [ ("call_mut", InstanceField.Method (fun ε τ α =>
        match ε, τ, α with
        | [], [], [self; Value.Tuple args] =>
          let* self := M.read self in
          M.call_closure Output self args
        | _, _, _ => M.impossible "wrong number of arguments"
        end
      )) ].

  Axiom FunctionImplementsFnOnce :
    forall (Args : list Ty.t) (Output : Ty.t),
    M.IsTraitInstance
      "core::ops::function::FnOnce"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) [Ty.tuple Args]
      (Ty.function Args Output)
      (* Instance *) [ ("call_once", InstanceField.Method (fun ε τ α =>
        match ε, τ, α with
        | [], [], [self; Value.Tuple args] =>
          M.call_closure Output self args
        | _, _, _ => M.impossible "wrong number of arguments"
        end
      )) ].
End FunctionTraitAutomaticImpl.
