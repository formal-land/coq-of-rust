Require Import CoqOfRust.CoqOfRust.
Require Export smpl.Smpl.

Import List.ListNotations.

Local Open Scope list.

Class Link (A : Set) : Set := {
  Φ : Ty.t;
  φ : A -> Value.t;
}.
(* We make explicit the argument [A]. *)
Arguments Φ _ {_}.

Global Opaque φ.

Smpl Create of_value.
Smpl Add reflexivity : of_value.

Module OfValue.
  Inductive t (value' : Value.t) : Type :=
  | Make {A : Set} `{Link A} (value : A) :
    value' = φ value ->
    t value'.

  Definition get_Set {value' : Value.t} (x : t value') : Set :=
    let '@Make _ A _ _ _ := x in
    A.

  Global Instance IsLink {value' : Value.t} (x : t value') : Link (get_Set x).
  Proof.
    destruct x.
    assumption.
  Defined.

  Definition get_value {value' : Value.t} (x : t value') : get_Set x :=
    let '@Make _ _ _ value _ := x in
    value.

  Definition of_value {A : Set} `{Link A} (value : A) :
    t (φ value).
  Proof.
    eapply Make with (value := value).
    reflexivity.
  Defined.
  Smpl Add apply of_value : of_value.
End OfValue.

Module Bool.
  Global Instance IsLink : Link bool := {
    Φ := Ty.path "bool";
    φ b := Value.Bool b;
  }.

  Lemma of_value_with (b : bool) :
    Value.Bool b = φ b.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (b : bool) :
    OfValue.t (Value.Bool b).
  Proof.
    eapply OfValue.Make with (A := bool); smpl of_value.
  Defined.
  Smpl Add apply of_value : of_value.
End Bool.

Module Integer.
  (** We distinguish the various forms of integers at this level. We will use plain [Z] integers in
      the simulations. *)
  Record t {kind : IntegerKind.t} : Set := {
    value : Z;
  }.
  Arguments t : clear implicits.

  Definition to_ty_path (kind : IntegerKind.t) : string :=
    match kind with
    | IntegerKind.I8 => "i8"
    | IntegerKind.I16 => "i16"
    | IntegerKind.I32 => "i32"
    | IntegerKind.I64 => "i64"
    | IntegerKind.I128 => "i128"
    | IntegerKind.Isize => "isize"
    | IntegerKind.U8 => "u8"
    | IntegerKind.U16 => "u16"
    | IntegerKind.U32 => "u32"
    | IntegerKind.U64 => "u64"
    | IntegerKind.U128 => "u128"
    | IntegerKind.Usize => "usize"
    end.

  Global Instance IsLink {kind : IntegerKind.t} : Link (t kind) := {
    Φ := Ty.path (to_ty_path kind);
    φ '{| value := value |} := Value.Integer kind value;
  }.

  Lemma of_value_with {kind : IntegerKind.t} (value : Z) :
    Value.Integer kind value = φ (Integer.Build_t kind value).
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value {kind : IntegerKind.t} (value : Z) :
    OfValue.t (Value.Integer kind value).
  Proof. eapply OfValue.Make with (A := t kind); smpl of_value. Defined.
  Smpl Add apply of_value : of_value.
End Integer.

(** ** Integer kinds for better readability *)
Module U8.
  Definition t : Set := Integer.t IntegerKind.U8.
End U8.

Module U16.
  Definition t : Set := Integer.t IntegerKind.U16.
End U16.

Module U32.
  Definition t : Set := Integer.t IntegerKind.U32.
End U32.

Module U64.
  Definition t : Set := Integer.t IntegerKind.U64.
End U64.

Module U128.
  Definition t : Set := Integer.t IntegerKind.U128.
End U128.

Module Usize.
  Definition t : Set := Integer.t IntegerKind.Usize.
End Usize.

Module I8.
  Definition t : Set := Integer.t IntegerKind.I8.
End I8.

Module I16.
  Definition t : Set := Integer.t IntegerKind.I16.
End I16.

Module I32.
  Definition t : Set := Integer.t IntegerKind.I32.
End I32.

Module I64.
  Definition t : Set := Integer.t IntegerKind.I64.
End I64.

Module I128.
  Definition t : Set := Integer.t IntegerKind.I128.
End I128.

Module Isize.
  Definition t : Set := Integer.t IntegerKind.Isize.
End Isize.

Module Char.
  Inductive t : Set :=
  | Make (c : Z).

  Global Instance IsLink : Link t := {
    Φ := Ty.path "char";
    φ '(Make c) := Value.UnicodeChar c;
  }.

  Lemma of_value_with (c : Z) :
    Value.UnicodeChar c = φ (Char.Make c).
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (c : Z) :
    OfValue.t (Value.UnicodeChar c).
  Proof. eapply OfValue.Make with (A := t); smpl of_value. Defined.
  Smpl Add apply of_value : of_value.
End Char.

(** ** Tuples *)
Module Never.
  Global Instance IsLink : Link Empty_set := {
    Φ := Ty.path "never";
    φ x := match x with end;
  }.
End Never.

Module Unit.
  Global Instance IsLink : Link unit := {
    Φ := Ty.tuple [];
    φ 'tt := Value.Tuple [];
  }.

  Lemma of_value_with :
    Value.Tuple [] = φ tt.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value :
    OfValue.t (Value.Tuple []).
  Proof. eapply OfValue.Make with (A := unit); smpl of_value. Defined.
  Smpl Add apply of_value : of_value.
End Unit.

Module OneElementTuple.
  (** There are no tuples of one element in Coq so we have to create it. This is different than the
      type itself in the sense that the [Link] instance should not be the same and use Rust tuples
      of one element instead. *)
  Record t {A : Set} `{Link A} : Set := {
    value : A;
  }.
  Arguments t _ {_}.

  Global Instance IsLink {A : Set} `{Link A} : Link (t A) := {
    Φ := Ty.tuple [Φ A];
    φ '{| value := value |} := Value.Tuple [φ value];
  }.

  Lemma of_value_with {A : Set} `{Link A} value value' :
    value' = φ value ->
    Value.Tuple [value'] = φ (OneElementTuple.Build_t A _ value).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (value' : Value.t) :
    OfValue.t value' ->
    OfValue.t (Value.Tuple [value']).
  Proof.
    intros [A].
    eapply OfValue.Make with (A := t A).
    smpl of_value; eassumption.
  Defined.
  Smpl Add apply of_value : of_value.
End OneElementTuple.

Module Pair.
  Global Instance IsLink (A1 A2 : Set)
      (_ : Link A1)
      (_ : Link A2) :
      Link (A1 * A2) := {
    Φ := Ty.tuple [Φ A1; Φ A2];
    φ '(a1, a2) := Value.Tuple [φ a1; φ a2];
  }.

  Lemma of_value_with {A1 A2 : Set} `{Link A1} `{Link A2} a1 a2 a1' a2' :
    a1' = φ a1 ->
    a2' = φ a2 ->
    Value.Tuple [a1'; a2'] = φ (A := A1 * A2) (a1, a2).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (a1' a2' : Value.t) :
    OfValue.t a1' ->
    OfValue.t a2' ->
    OfValue.t (Value.Tuple [a1'; a2']).
  Proof.
    intros [A1] [A2].
    eapply OfValue.Make with (A := A1 * A2).
    smpl of_value; eassumption.
  Defined.
  Smpl Add apply of_value : of_value.
End Pair.

(** A general type for references. Can be used for mutable or non-mutable references, as well as
    for unsafe pointers (we assume that the `unsafe` code is safe). *)
Module Ref.
  Module Core.
    Inductive t (A : Set) `{Link A} : Set :=
    | Immediate (value : A)
    | Mutable {Address Big_A : Set}
      (address : Address)
      (path : Pointer.Path.t)
      (big_to_value : Big_A -> Value.t)
      (projection : Big_A -> option A)
      (injection : Big_A -> A -> option Big_A).
    Arguments Immediate {_ _}.
    Arguments Mutable {_ _ _ _}.

    Definition to_core {A : Set} `{Link A} (ref : t A) : Pointer.Core.t Value.t :=
      match ref with
      | Immediate value =>
        Pointer.Core.Immediate (φ value)
      | Mutable address path big_to_value projection injection =>
        Pointer.Core.Mutable address path
      end.
  End Core.

  Record t {kind : Pointer.Kind.t} {A : Set} `{Link A} : Set := {
    core : Core.t A;
  }.
  Arguments t _ _ {_}.

  Definition to_core {kind : Pointer.Kind.t} {A : Set} `{Link A} (ref : t kind A) :
      Pointer.Core.t Value.t :=
    Core.to_core ref.(core).

  Definition to_pointer {kind : Pointer.Kind.t} {A : Set} `{Link A} (ref : t kind A) :
      Pointer.t Value.t :=
    {|
      Pointer.kind := kind;
      Pointer.core := to_core ref;
    |}.

  Global Instance IsLink {kind : Pointer.Kind.t} {A : Set} `{Link A} : Link (t kind A) := {
    Φ := Ty.apply (Ty.path (Pointer.Kind.to_ty_path kind)) [] [Φ A];
    φ ref := Value.Pointer (to_pointer ref);
  }.

  Definition immediate (kind : Pointer.Kind.t) {A : Set} `{Link A} (value : A) : t kind A :=
    {| core := Core.Immediate value |}.

  Definition deref {kind : Pointer.Kind.t} {A : Set} `{Link A} (ref : t kind A) :
      t Pointer.Kind.Raw A :=
    {| core := ref.(core) |}.

  Definition cast {kind1 kind2 : Pointer.Kind.t} {A : Set} `{Link A} (ref : t kind1 A) :
      t kind2 A :=
    {| core := ref.(core) |}.

  Lemma deref_eq {kind : Pointer.Kind.t} {A : Set} `{Link A} (ref : t kind A) :
    M.deref (φ ref) = M.pure (φ (deref ref)).
  Proof.
    reflexivity.
  Qed.

  (** We can make the conversion of values for immediate pointers that are used in Rust `const`. *)
  Lemma of_value_with {A : Set} `{Link A} (value : A) value' :
    value' = φ value ->
    Value.Pointer {|
      Pointer.kind := Pointer.Kind.Raw;
      Pointer.core := Pointer.Core.Immediate value';
    |} = φ (immediate Pointer.Kind.Raw value).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (value' : Value.t) :
    OfValue.t value' ->
    OfValue.t (Value.Pointer {|
      Pointer.kind := Pointer.Kind.Raw;
      Pointer.core := Pointer.Core.Immediate value';
    |}).
  Proof.
    intros [A].
    eapply OfValue.Make with (A := t Pointer.Kind.Raw A).
    smpl of_value; eassumption.
  Defined.
  Smpl Add apply of_value : of_value.
End Ref.

Module SubPointer.
  Module Runner.
    (** We group in a single data structure how we can access to the address of a field of a value
        pointed by a pointer. The field is given by [index]. The functions [projection]
        and [injection] are to read or update values at this [index], once we have a typed
        representation. These operations can fail if the field is from an enum case that is not the
        one currently selected. *)
    Record t (A Sub_A : Set) {H_A : Link A} {H_Sub_A : Link Sub_A} : Set := {
      index : Pointer.Index.t;
      projection : A -> option Sub_A;
      injection : A -> Sub_A -> option A;
    }.
    Arguments index {_ _ _ _}.
    Arguments projection {_ _ _ _}.
    Arguments injection {_ _ _ _}.

    Module Valid.
      (** What does it mean for a [runner] to be well formed. *)
      Record t {A Sub_A : Set} `{Link A} `{Link Sub_A} (runner : Runner.t A Sub_A) : Prop := {
        read_commutativity (a : A) :
          Option.map (runner.(projection) a) φ =
          Value.read_index (φ a) runner.(index);
        write_commutativity (a : A) (sub_a : Sub_A) :
          Option.map (runner.(injection) a sub_a) φ =
          Value.write_index (φ a) runner.(index) (φ sub_a);
      }.
    End Valid.
  End Runner.
End SubPointer.

Module IsSubPointer.
  (** If a pointer (the sub-pointer) targets the field given by a [runner] of another value
      targeted by a pointer. We only consider the core part of a pointer. *)
  Inductive t {A Sub_A : Set} `{Link A} `{Link Sub_A}
      (runner : SubPointer.Runner.t A Sub_A) : Ref.Core.t A -> Ref.Core.t Sub_A -> Set :=
  | Immediate (value : A) (sub_value : Sub_A) :
    runner.(SubPointer.Runner.projection) value = Some sub_value ->
    t runner
      (Ref.Core.Immediate value)
      (Ref.Core.Immediate sub_value)
  | Mutable {Address Big_A : Set}
      (address : Address)
      (path : Pointer.Path.t)
      (big_to_value : Big_A -> Value.t)
      (projection : Big_A -> option A)
      (injection : Big_A -> A -> option Big_A) :
    let ref : Ref.Core.t A :=
      Ref.Core.Mutable address path big_to_value projection injection in
    let sub_ref : Ref.Core.t Sub_A :=
      Ref.Core.Mutable
        address
        (path ++ [runner.(SubPointer.Runner.index)])
        big_to_value
        (fun (big_a : Big_A) =>
          match projection big_a with
          | Some a => runner.(SubPointer.Runner.projection) a
          | None => None
          end : option Sub_A
        )
        (fun (big_a : Big_A) (new_sub_a : Sub_A) =>
          match projection big_a with
          | Some a =>
            match runner.(SubPointer.Runner.injection) a new_sub_a with
            | Some new_a => injection big_a new_a
            | None => None
            end
          | None => None
          end : option Big_A
        ) in
    t runner ref sub_ref.
End IsSubPointer.

(** Some convenient `output_to_value` functions. *)

Definition output_pure (Output : Set) `{Link Output} (output : Output) : Value.t + Exception.t :=
  inl (φ output).

Module Output.
  Module Exception.
    Inductive t (R : Set) : Set :=
    | Return (return_ : R)
    | Break
    | Continue
    | Panic (panic : Panic.t).
    Arguments Return {_}.
    Arguments Break {_}.
    Arguments Continue {_}.
    Arguments Panic {_}.

    Definition to_exception {R : Set} `{Link R} (exception : t R) : M.Exception.t :=
      match exception with
      | Return return_ => M.Exception.Return (φ return_)
      | Break => M.Exception.Break
      | Continue => M.Exception.Continue
      | Panic panic => M.Exception.Panic panic
      end.

    Smpl Create of_output.

    Lemma of_return_eq {R : Set} `{Link R} (return_ : R) return_' :
      return_' = φ return_ ->
      M.Exception.Return return_' = to_exception (Return return_).
    Proof. now intros; subst. Qed.
    Smpl Add apply of_return_eq : of_output.

    Lemma of_break_eq {R : Set} `{Link R} :
      M.Exception.Break = to_exception Break.
    Proof. reflexivity. Qed.
    Smpl Add apply of_break_eq : of_output.

    Lemma of_continue_eq {R : Set} `{Link R} :
      M.Exception.Continue = to_exception Continue.
    Proof. reflexivity. Qed.
    Smpl Add apply of_continue_eq : of_output.

    Lemma of_panic_eq {R : Set} `{Link R} panic :
      M.Exception.Panic panic = to_exception (Panic panic).
    Proof. reflexivity. Qed.
    Smpl Add apply of_panic_eq : of_output.
  End Exception.

  Inductive t (R Output : Set) : Set :=
  | Success (output : Output) : t R Output
  | Exception (exception : Exception.t R) : t R Output.
  Arguments Success {_ _}.
  Arguments Exception {_ _}.

  Definition to_value {R Output : Set} `{Link R} `{Link Output} (output : t R Output) :
      Value.t + M.Exception.t :=
    match output with
    | Success output => output_pure Output output
    | Exception exception => inr (Exception.to_exception exception)
    end.

  Lemma of_success_eq {R Output : Set} `{Link R} `{Link Output}
      (output : Output) output' :
    output' = φ output ->
    inl output' = to_value (Output.Success (R := R) output).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_success_eq : of_output.

  Lemma of_exception_eq {R Output : Set} `{Link R} `{Link Output}
      (exception : Exception.t R) (exception' : M.Exception.t) :
    exception' = Exception.to_exception exception ->
    inr exception' = to_value (Output.Exception (R := R) exception).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_exception_eq : of_output.
End Output.

(** For the output of closure calls, where we know it can only be a success or panic, but not a
    `return`, `break`, or `continue`. *)
Module SuccessOrPanic.
  Inductive t (Output : Set) : Set :=
  | Success (output : Output)
  | Panic (panic : Panic.t).
  Arguments Success {_}.
  Arguments Panic {_}.

  Definition to_value {Output : Set} `{Link Output} (output : t Output) :
      Value.t + M.Exception.t :=
    match output with
    | Success output => inl (φ output)
    | Panic panic => inr (M.Exception.Panic panic)
    end.
End SuccessOrPanic.

Module Run.
  Reserved Notation "{{ e 🔽 R , Output }}" (no associativity).

  (** The [Run.t] predicate to show that there exists a trace of execution for an expression [e]
      if we choose the right types/`φ` functions and make a valid names and traits
      resolution.

      The function [output_to_value] is used to convert the output of the expression [e] to
      a [Value.t] or an [Exception.t] at the end. It gives a constraint on what kinds of results
      the expression [e] can produce.
  *)
  Inductive t (R Output : Set) `{Link R} `{Link Output} : M -> Set :=
  | Pure
      (output : Output.t R Output)
      (output' : Value.t + Exception.t) :
    output' = Output.to_value output ->
    {{ LowM.Pure output' 🔽 R, Output }}
  | CallPrimitiveStateAlloc
      (value' : Value.t)
      (k : Value.t -> M)
      (of_value : OfValue.t value') :
    (forall (ref : Ref.t Pointer.Kind.Raw (OfValue.get_Set of_value)),
      {{ k (φ ref) 🔽 R, Output }}
    ) ->
    {{ LowM.CallPrimitive (Primitive.StateAlloc value') k 🔽 R, Output }}
  | CallPrimitiveStateAllocImmediate
      (value' : Value.t)
      (k : Value.t -> M)
      (of_value : OfValue.t value') :
    {{
      k (φ (Ref.immediate Pointer.Kind.Raw (OfValue.get_value of_value))) 🔽
      R, Output
    }} ->
    {{ LowM.CallPrimitive (Primitive.StateAlloc value') k 🔽 R, Output }}
  | CallPrimitiveStateRead {A : Set} `{Link A}
      (ref_core : Ref.Core.t A)
      (k : Value.t -> M) :
    let ref : Ref.t Pointer.Kind.Raw A := {| Ref.core := ref_core |} in
    (forall (value : A),
      {{ k (φ value) 🔽 R, Output }}
    ) ->
    (* We can expect the pointers to always be the image of [φ] as they cannot be manually
       created. This is the same for the other primitives expecting a pointer. *)
    {{ LowM.CallPrimitive (Primitive.StateRead (φ ref)) k 🔽 R, Output }}
  | CallPrimitiveStateReadImmediate {A : Set} `{Link A}
      (value : A)
      (k : Value.t -> M) :
    let ref := Ref.immediate Pointer.Kind.Raw value in
    {{ k (φ value) 🔽 R, Output }} ->
    {{ LowM.CallPrimitive (Primitive.StateRead (φ ref)) k 🔽 R, Output }}
  | CallPrimitiveStateWrite {A : Set} `{Link A}
      (ref_core : Ref.Core.t A)
      (value : A) (value' : Value.t)
      (k : Value.t -> M) :
    let ref : Ref.t Pointer.Kind.Raw A := {| Ref.core := ref_core |} in
    value' = φ value ->
    {{ k (φ tt) 🔽 R, Output }} ->
    {{ LowM.CallPrimitive (Primitive.StateWrite (φ ref) value') k 🔽 R, Output }}
  | CallPrimitiveGetSubPointer {A Sub_A : Set} `{Link A} `{Link Sub_A}
      (ref_core : Ref.Core.t A)
      (runner : SubPointer.Runner.t A Sub_A)
      (k : Value.t -> M) :
    let ref : Ref.t Pointer.Kind.Raw A := {| Ref.core := ref_core |} in
    SubPointer.Runner.Valid.t runner ->
    (forall (sub_ref : Ref.t Pointer.Kind.Raw Sub_A),
      {{ k (φ sub_ref) 🔽 R, Output }}
    ) ->
    {{
      LowM.CallPrimitive (Primitive.GetSubPointer (φ ref) runner.(SubPointer.Runner.index)) k 🔽
      R, Output
    }}
  | CallPrimitiveAreEqual {A : Set} `{Link A}
      (x y : A) (x' y' : Value.t)
      (k : Value.t -> M) :
    x' = φ x ->
    y' = φ y ->
    (forall (b : bool),
      {{ k (φ b) 🔽 R, Output }}
    ) ->
    {{
      LowM.CallPrimitive (Primitive.AreEqual x' y') k 🔽
      R, Output
    }}
  | CallPrimitiveGetFunction
      (name : string) (generic_consts : list Value.t) (generic_tys : list Ty.t)
      (function : PolymorphicFunction.t)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (function generic_consts generic_tys)) in
    M.IsFunction name function ->
    {{ k closure 🔽 R, Output }} ->
    {{
      LowM.CallPrimitive (Primitive.GetFunction name generic_consts generic_tys) k 🔽
      R, Output
    }}
  | CallPrimitiveGetAssociatedFunction
      (ty : Ty.t) (name : string) (generic_consts : list Value.t) (generic_tys : list Ty.t)
      (associated_function : PolymorphicFunction.t)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (associated_function generic_consts generic_tys)) in
    M.IsAssociatedFunction ty name associated_function ->
    {{ k closure 🔽 R, Output }} ->
    {{ LowM.CallPrimitive
        (Primitive.GetAssociatedFunction ty name generic_consts generic_tys) k 🔽
        R, Output
    }}
  | CallPrimitiveGetTraitMethod
      (trait_name : string) (self_ty : Ty.t) (trait_consts : list Value.t) (trait_tys : list Ty.t)
      (method_name : string) (generic_consts : list Value.t) (generic_tys : list Ty.t)
      (method : PolymorphicFunction.t)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (method generic_consts generic_tys)) in
    IsTraitMethod.t trait_name self_ty trait_tys method_name method ->
    {{ k closure 🔽 R, Output }} ->
    {{ LowM.CallPrimitive
        (Primitive.GetTraitMethod
          trait_name
          self_ty
          trait_consts
          trait_tys
          method_name
          generic_consts
          generic_tys
        )
        k 🔽
        R, Output
    }}
  | CallClosure {Output' : Set}
      (ty : Ty.t) (to_value : Output' -> Value.t)
      (f : list Value.t -> M) (args : list Value.t)
      (k : Value.t + Exception.t -> M) :
    let _ := Build_Link _ ty to_value in
    let closure := Value.Closure (existS (_, _) f) in
    {{ f args 🔽 Output', Output' }} ->
    (forall (value_inter : SuccessOrPanic.t Output'),
      {{ k (SuccessOrPanic.to_value value_inter) 🔽 R, Output }}
    ) ->
    {{ LowM.CallClosure closure args k 🔽 R, Output }}
  | Let {Output' : Set}
      (ty : Ty.t) (to_value : Output' -> Value.t)
      (e : M) (k : Value.t + Exception.t -> M) :
    let _ := Build_Link _ ty to_value in
    {{ e 🔽 R, Output' }} ->
    (forall (value_inter : Output.t R Output'),
      {{ k (Output.to_value value_inter) 🔽 R, Output }}
    ) ->
    {{ LowM.Let e k 🔽 R, Output }}
  (** This primitive is useful to avoid blocking the reduction of this inductive with a [rewrite]
      that is hard to eliminate. *)
  | Rewrite (e e' : M) :
    e = e' ->
    {{ e' 🔽 R, Output }} ->
    {{ e 🔽 R, Output }}

  where "{{ e 🔽 R , Output }}" :=
    (t R Output e).

  Notation "{{ e 🔽 Output }}" := ({{ e 🔽 Output , Output }}).
End Run.

Import Run.

Module Primitive.
  (** These primitives are equivalent to the ones in the generated code, except that we are now
      with types. We have also removed the primitives related to name/trait resolution, as this is
      now done. *)
  Inductive t : Set -> Set :=
  | StateAlloc {A : Set} `{Link A} (value : A) : t (Ref.Core.t A)
  | StateRead {A : Set} `{Link A} (ref_core : Ref.Core.t A) : t A
  | StateWrite {A : Set} `{Link A} (ref_core : Ref.Core.t A) (value : A) : t unit
  | GetSubPointer {A Sub_A : Set} `{Link A} `{Link Sub_A}
    (ref_core : Ref.Core.t A) (runner : SubPointer.Runner.t A Sub_A) :
    t (Ref.Core.t Sub_A)
  | AreEqual {A : Set} `{Link A} (x y : A) : t bool.
End Primitive.

Module LowM.
  (** The typed version of the [LowM.t] monad used in the generated code. We might need to use a
      co-inductive definition instead at some point. *)
  Inductive t (R Output : Set) : Set :=
  | Pure (value : Output.t R Output)
  | CallPrimitive {A : Set} (primitive : Primitive.t A) (k : A -> t R Output)
  | Let {A : Set} (e : t R A) (k : Output.t R A -> t R Output)
  | Call {A : Set} (e : t A A) (k : SuccessOrPanic.t A -> t R Output)
  | Loop {A : Set} (body : t R A) (k : A -> t R Output).
  Arguments Pure {_ _}.
  Arguments CallPrimitive {_ _ _}.
  Arguments Let {_ _ _}.
  Arguments Call {_ _ _}.
  Arguments Loop {_ _ _}.
End LowM.

(* We do not define an equivalent of [M] as the resulting term is generated, so we are not
   interested into having syntactic sugar for the error monad. *)

(** With this function we generate an expression in [LowM.t Output] that is equivalent to the
    input [e] expression, following the proof of equivalence provided in [run]. *)
Fixpoint evaluate {R Output : Set} `{Link R} `{Link Output} {e : M}
    (run : {{ e 🔽 R, Output }}) :
  LowM.t R Output.
Proof.
  destruct run.
  { (* Pure *)
    exact (LowM.Pure output).
  }
  { (* Alloc *)
    apply (LowM.CallPrimitive (Primitive.StateAlloc (OfValue.get_value of_value))).
    intros ref_core.
    eapply evaluate.
    match goal with
    | H : forall _, _ |- _ => apply (H {| Ref.core := ref_core |})
    end.
  }
  { (* AllocImmediate *)
    exact (evaluate _ _ _ _ _ run).
  }
  { (* Read *)
    apply (LowM.CallPrimitive (Primitive.StateRead ref_core)).
    intros value.
    eapply evaluate.
    match goal with
    | H : forall _, _ |- _ => apply (H value)
    end.
  }
  { (* ReadImmediate *)
    exact (evaluate _ _ _ _ _ run).
  }
  { (* Write *)
    apply (LowM.CallPrimitive (Primitive.StateWrite ref_core value)).
    intros _.
    exact (evaluate _ _ _ _ _ run).
  }
  { (* SubPointer *)
    apply (LowM.CallPrimitive (Primitive.GetSubPointer ref_core runner)).
    intros sub_ref_core.
    eapply evaluate.
    match goal with
    | H : forall _, _ |- _ => apply (H {| Ref.core := sub_ref_core |})
    end.
  }
  { (* AreEqual *)
    apply (LowM.CallPrimitive (Primitive.AreEqual x y)).
    intros b.
    eapply evaluate.
    match goal with
    | H : forall _, _ |- _ => apply (H b)
    end.

  }
  { (* CallPrimitiveGetFunction *)
    exact (evaluate _ _ _ _ _ run).
  }
  { (* CallPrimitiveGetAssociatedFunction *)
    exact (evaluate _ _ _ _ _ run).
  }
  { (* CallPrimitiveGetTraitMethod *)
    exact (evaluate _ _ _ _ _ run).
  }
  { (* CallClosure *)
    eapply LowM.Call. {
      exact (evaluate _ _ _ _ _ run).
    }
    intros output'; eapply evaluate.
    match goal with
    | H : forall _ : SuccessOrPanic.t Output', _ |- _ => apply (H output')
    end.
  }
  { (* Let *)
    eapply LowM.Let. {
      exact (evaluate _ _ _ _ _ run).
    }
    intros output'; eapply evaluate.
    match goal with
    | H : forall _ : Output.t _ Output', _ |- _ => apply (H output')
    end.
  }
  { (* Rewrite *)
    exact (evaluate _ _ _ _ _ run).
  }
Defined.

Ltac run_symbolic_pure :=
  eapply Run.Pure;
    try reflexivity;
    repeat smpl of_output;
    repeat smpl of_value.

Ltac run_symbolic_state_alloc_immediate :=
  unshelve eapply Run.CallPrimitiveStateAllocImmediate; [smpl of_value |].

Ltac run_symbolic_state_read :=
  eapply Run.CallPrimitiveStateRead;
  intros.

Ltac run_symbolic_state_read_immediate :=
  cbn;
  apply Run.CallPrimitiveStateReadImmediate.

Ltac run_symbolic_state_write :=
  eapply Run.CallPrimitiveStateWrite; [smpl of_value |].

Ltac run_rewrite_deref :=
  eapply Run.Rewrite; [
    rewrite Ref.deref_eq;
    reflexivity
  |].

Ltac run_symbolic_one_step_immediate :=
  match goal with
  | |- {{ _ 🔽 _, _ }} =>
    run_symbolic_pure ||
    run_symbolic_state_alloc_immediate ||
    run_symbolic_state_read_immediate ||
    run_symbolic_state_read ||
    run_symbolic_state_write ||
    run_rewrite_deref ||
    fold @LowM.let_ ||
    cbn
  end.

Smpl Create run_symbolic.

(** We should use this tactic instead of the ones above, as this one calls all the others. *)
Ltac run_symbolic :=
  repeat (
    run_symbolic_one_step_immediate ||
    smpl run_symbolic
  ).

(** For the specific case of sub-pointers, we still do it by hand by providing the corresponding
    validity statement for the index that we access. *)
Ltac run_sub_pointer sub_pointer_is_valid :=
  cbn; apply (Run.CallPrimitiveGetSubPointer _ _ _ _ _ sub_pointer_is_valid); intros.

Module Function2.
  Record t {A1 A2 Output : Set} `{Link A1} `{Link A2} `{Link Output} : Set := {
    f : list Value.t -> M;
    run : forall (a1 : A1) (a2 : A2),
      {{ f [ φ a1; φ a2 ] 🔽 Output }};
  }.
  Arguments t _ _ _ {_ _ _}.

  Global Instance IsLink (A1 A2 Output : Set) `{Link A1} `{Link A2} `{Link Output} :
      Link (t A1 A2 Output) := {
    Φ := Ty.function [Φ A1; Φ A2] (Φ Output);
    φ x := Value.Closure (existS (_, _) x.(f));
  }.
End Function2.
