Require Import CoqOfRust.CoqOfRust.

Import List.ListNotations.

Local Open Scope list.

Class Link (A : Set) : Set := {
  to_ty : Ty.t;
  to_value : A -> Value.t;
}.
(* We make explicit the argument [A]. *)
Arguments to_ty _ {_}.

Global Instance BoolIsLink : Link bool := {
  to_ty := Ty.path "bool";
  to_value b := Value.Bool b;
}.

Module Integer.
  (** We distinguish the various forms of integers at this level. We will use plain [Z] integers in
      the simulations. *)
  Inductive t (kind : IntegerKind.t) : Set :=
  | Make (i : Z).
  Arguments Make {_}.

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
    to_ty := Ty.path (to_ty_path kind);
    to_value '(Make i) := Value.Integer kind i;
  }.
End Integer.

Module Char.
  Inductive t : Set :=
  | Make (c : Z).

  Global Instance IsLink : Link t := {
    to_ty := Ty.path "char";
    to_value '(Make c) := Value.UnicodeChar c;
  }.
End Char.

Module OneElementTuple.
  (** There are no tuples of one element in Coq so we have to create it. This is different than the
      type itself in the sense that the [Link] instance should not be the same and use Rust tuples
      of one element instead. *)
  Inductive t (A : Set) `{Link A} : Set :=
  | Make (a : A).
  Arguments Make {_ _}.

  Global Instance IsLink {A : Set} `{Link A} : Link (t A) := {
    to_ty := Ty.tuple [to_ty A];
    to_value '(Make a) := Value.Tuple [to_value a];
  }.
End OneElementTuple.

Module TupleIsLink.
  Global Instance I0 : Link unit := {
    to_ty := Ty.tuple [];
    to_value _ := Value.Tuple [];
  }.

  Global Instance I2 (A1 A2 : Set)
      (_ : Link A1)
      (_ : Link A2) :
      Link (A1 * A2) := {
    to_ty := Ty.tuple [to_ty A1; to_ty A2];
    to_value '(a1, a2) := Value.Tuple [to_value a1; to_value a2];
  }.

  Global Instance I3 (A1 A2 A3 : Set)
      (_ : Link A1)
      (_ : Link A2)
      (_ : Link A3) :
      Link (A1 * A2 * A3) := {
    to_ty := Ty.tuple [to_ty A1; to_ty A2; to_ty A3];
    to_value '(a1, a2, a3) := Value.Tuple [to_value a1; to_value a2; to_value a3];
  }.

  Global Instance I4 (A1 A2 A3 A4 : Set)
      (_ : Link A1)
      (_ : Link A2)
      (_ : Link A3)
      (_ : Link A4) :
      Link (A1 * A2 * A3 * A4) := {
    to_ty := Ty.tuple [to_ty A1; to_ty A2; to_ty A3; to_ty A4];
    to_value '(a1, a2, a3, a4) :=
      Value.Tuple [to_value a1; to_value a2; to_value a3; to_value a4];
  }.

  Global Instance I5 (A1 A2 A3 A4 A5 : Set)
      (_ : Link A1)
      (_ : Link A2)
      (_ : Link A3)
      (_ : Link A4)
      (_ : Link A5) :
      Link (A1 * A2 * A3 * A4 * A5) := {
    to_ty := Ty.tuple [to_ty A1; to_ty A2; to_ty A3; to_ty A4; to_ty A5];
    to_value '(a1, a2, a3, a4, a5) :=
      Value.Tuple [to_value a1; to_value a2; to_value a3; to_value a4; to_value a5];
  }.

  Global Instance I6 (A1 A2 A3 A4 A5 A6 : Set)
      (_ : Link A1)
      (_ : Link A2)
      (_ : Link A3)
      (_ : Link A4)
      (_ : Link A5)
      (_ : Link A6) :
      Link (A1 * A2 * A3 * A4 * A5 * A6) := {
    to_ty := Ty.tuple [to_ty A1; to_ty A2; to_ty A3; to_ty A4; to_ty A5; to_ty A6];
    to_value '(a1, a2, a3, a4, a5, a6) :=
      Value.Tuple [to_value a1; to_value a2; to_value a3; to_value a4; to_value a5; to_value a6];
  }.

  Global Instance I7 (A1 A2 A3 A4 A5 A6 A7 : Set)
      (_ : Link A1)
      (_ : Link A2)
      (_ : Link A3)
      (_ : Link A4)
      (_ : Link A5)
      (_ : Link A6)
      (_ : Link A7) :
      Link (A1 * A2 * A3 * A4 * A5 * A6 * A7) := {
    to_ty := Ty.tuple [to_ty A1; to_ty A2; to_ty A3; to_ty A4; to_ty A5; to_ty A6; to_ty A7];
    to_value '(a1, a2, a3, a4, a5, a6, a7) :=
      Value.Tuple [
        to_value a1; to_value a2; to_value a3; to_value a4; to_value a5; to_value a6; to_value a7
      ];
  }.

  Global Instance I8 (A1 A2 A3 A4 A5 A6 A7 A8 : Set)
      (_ : Link A1)
      (_ : Link A2)
      (_ : Link A3)
      (_ : Link A4)
      (_ : Link A5)
      (_ : Link A6)
      (_ : Link A7)
      (_ : Link A8) :
      Link (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8) := {
    to_ty := Ty.tuple [
      to_ty A1; to_ty A2; to_ty A3; to_ty A4; to_ty A5; to_ty A6; to_ty A7; to_ty A8
    ];
    to_value '(a1, a2, a3, a4, a5, a6, a7, a8) :=
      Value.Tuple [
        to_value a1;
        to_value a2;
        to_value a3;
        to_value a4;
        to_value a5;
        to_value a6;
        to_value a7;
        to_value a8
      ];
  }.
End TupleIsLink.

Module Ref.
  (** A general type for references. Can be used for mutable or non-mutable references, as well as
      for unsafe pointers (we assume that the `unsafe` code is safe). *)
  Inductive t (kind : Pointer.Kind.t) (A : Set) `{Link A} : Set :=
  | Immediate (value : A)
  | Mutable {Address Big_A : Set}
    (address : Address)
    (path : Pointer.Path.t)
    (big_to_value : Big_A -> Value.t)
    (projection : Big_A -> option A)
    (injection : Big_A -> A -> option Big_A).
  Arguments Immediate _ {_ _}.
  Arguments Mutable _ {_ _ _ _}.

  Definition to_core {kind : Pointer.Kind.t} {A : Set} `{Link A} (ref : t kind A) :
      Pointer.Core.t Value.t A :=
    match ref with
    | Immediate _ value =>
      Pointer.Core.Immediate (to_value value)
    | Mutable _ address path big_to_value projection injection =>
      Pointer.Core.Mutable (Pointer.Mutable.Make
        address path big_to_value projection injection
      )
    end.

  Definition to_pointer {kind : Pointer.Kind.t} {A : Set} `{Link A} (ref : t kind A) :
      Pointer.t Value.t :=
    Pointer.Make kind (to_ty A) to_value (to_core ref).

  Global Instance IsLink {kind : Pointer.Kind.t} {A : Set} `{Link A} : Link (t kind A) := {
    to_ty := Ty.apply (Ty.path (Pointer.Kind.to_ty_path kind)) [] [to_ty A];
    to_value ref := Value.Pointer (to_pointer ref);
  }.
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
          Option.map (runner.(projection) a) to_value =
          Value.read_index (to_value a) runner.(index);
        write_commutativity (a : A) (sub_a : Sub_A) :
          Option.map (runner.(injection) a sub_a) to_value =
          Value.write_index (to_value a) runner.(index) (to_value sub_a);
      }.
    End Valid.
  End Runner.
End SubPointer.

Module IsSubPointer.
  (** If a pointer (the sub-pointer) targets the field given by a [runner] of another value
      targetted by a pointer. *)
  Inductive t {kind : Pointer.Kind.t} {A Sub_A : Set} `{Link A} `{Link Sub_A}
      (runner : SubPointer.Runner.t A Sub_A) : Ref.t kind A -> Ref.t kind Sub_A -> Set :=
  | Immediate (value : A) (sub_value : Sub_A) :
    runner.(SubPointer.Runner.projection) value = Some sub_value ->
    t runner
      (Ref.Immediate kind value)
      (Ref.Immediate kind sub_value)
  | Mutable {Address Big_A : Set}
      (address : Address)
      (path : Pointer.Path.t)
      (big_to_value : Big_A -> Value.t)
      (projection : Big_A -> option A)
      (injection : Big_A -> A -> option Big_A) :
    let ref : Ref.t kind A :=
      Ref.Mutable kind address path big_to_value projection injection in
    let sub_ref : Ref.t kind Sub_A :=
      Ref.Mutable
        kind
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
  inl (to_value output).

Definition output_with_panic (Output : Set) `{Link Output} (output : Output + Panic.t) :
    Value.t + Exception.t :=
  match output with
  | inl output => inl (to_value output)
  | inr panic => inr (Exception.Panic panic)
  end.

Definition output_with_exception (Output : Set) `{Link Output} (output : Output + Exception.t) :
    Value.t + Exception.t :=
  match output with
  | inl output => inl (to_value output)
  | inr exception => inr exception
  end.

Module Run.
  Reserved Notation "{{ e ⇓ output_to_value }}" (at level 70, no associativity).

  (** The [Run.t] predicate to show that there exists a trace of execution for an expression [e]
      if we choose the right types/`to_value` functions and make a valid names and traits
      resolution.

      The function [output_to_value] is used to convert the output of the expression [e] to
      a [Value.t] or an [Exception.t] at the end. It gives a constraint on what kinds of results
      the expression [e] can produce.
  *)
  Inductive t {Output : Set} (output_to_value : Output -> Value.t + Exception.t) : M -> Set :=
  | Pure
      (output : Output)
      (output' : Value.t + Exception.t) :
    output' = output_to_value output ->
    {{ LowM.Pure output' ⇓ output_to_value }}
  | CallPrimitiveStateAlloc {A : Set} `{Link A}
      (kind : Pointer.Kind.t)
      (value : A) (value' : Value.t)
      (k : Value.t -> M) :
    value' = to_value value ->
    (forall (ref : Ref.t kind A),
      {{ k (to_value ref) ⇓ output_to_value }}
     ) ->
    {{ LowM.CallPrimitive (Primitive.StateAlloc value') k ⇓ output_to_value }}
  | CallPrimitiveStateAllocImmediate {A : Set} `{Link A}
      (kind : Pointer.Kind.t)
      (value : A) (value' : Value.t)
      (k : Value.t -> M) :
    value' = to_value value ->
    {{ k (to_value (Ref.Immediate kind value)) ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive (Primitive.StateAlloc value') k ⇓ output_to_value }}
  | CallPrimitiveStateRead {kind : Pointer.Kind.t} {A : Set}
      (* We make the [ty] and [to_value] explicit instead of using the class to avoid inference
         problems. *)
      (ty : Ty.t) (to_value : A -> Value.t)
      (ref : @Ref.t kind A {| to_ty := ty; to_value := to_value |})
      (pointer_core : Pointer.Core.t Value.t A)
      (k : Value.t -> M) :
    let pointer := Pointer.Make kind ty to_value pointer_core in
    pointer_core = Ref.to_core ref ->
    (forall (value : A),
      {{ k (to_value value) ⇓ output_to_value }}
    ) ->
    {{ LowM.CallPrimitive (Primitive.StateRead pointer) k ⇓ output_to_value }}
  | CallPrimitiveStateReadImmediate {kind : Pointer.Kind.t} {A : Set}
      (* Same as with read, we make the [Link] class explicit. *)
      (ty : Ty.t) (to_value : A -> Value.t)
      (value : A)
      (pointer_core : Pointer.Core.t Value.t A)
      (k : Value.t -> M) :
    let pointer := Pointer.Make kind ty to_value pointer_core in
    let ref := @Ref.Immediate kind A {| to_ty := ty; to_value := to_value |} value in
    pointer_core = Ref.to_core ref ->
    {{ k (to_value value) ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive (Primitive.StateRead pointer) k ⇓ output_to_value }}
  | CallPrimitiveStateWrite {kind : Pointer.Kind.t} {A : Set}
      (* Same as with read, we make the [Link] class explicit. *)
      (ty : Ty.t) (to_value : A -> Value.t)
      (ref : @Ref.t kind A {| to_ty := ty; to_value := to_value |})
      (pointer_core : Pointer.Core.t Value.t A)
      (value : A) (value' : Value.t)
      (k : Value.t -> M) :
    let pointer := Pointer.Make kind ty to_value pointer_core in
    pointer_core = Ref.to_core ref ->
    value' = to_value value ->
    {{ k (Value.Tuple []) ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive (Primitive.StateWrite pointer value') k ⇓ output_to_value }}
  | CallPrimitiveGetSubPointer {kind : Pointer.Kind.t} {A Sub_A : Set} `{Link A} `{Link Sub_A}
      (ref : Ref.t kind A) (pointer : Pointer.t Value.t)
      (runner : SubPointer.Runner.t A Sub_A)
      (k : Value.t -> M) :
    pointer = Ref.to_pointer ref ->
    SubPointer.Runner.Valid.t runner ->
    (forall (sub_ref : Ref.t kind Sub_A),
      let sub_pointer := Ref.to_pointer sub_ref in
      {{ k (Value.Pointer sub_pointer) ⇓ output_to_value }}
    ) ->
    {{
      LowM.CallPrimitive (Primitive.GetSubPointer pointer runner.(SubPointer.Runner.index)) k ⇓
      output_to_value
    }}
  | CallPrimitiveGetFunction
      (name : string) (generic_consts : list Value.t) (generic_tys : list Ty.t)
      (function : PolymorphicFunction.t)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (function generic_consts generic_tys)) in
    M.IsFunction name function ->
    {{ k closure ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive (Primitive.GetFunction name generic_tys) k ⇓ output_to_value }}
  | CallPrimitiveGetAssociatedFunction
      (ty : Ty.t) (name : string) (generic_consts : list Value.t) (generic_tys : list Ty.t)
      (associated_function : PolymorphicFunction.t)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (associated_function generic_consts generic_tys)) in
    M.IsAssociatedFunction ty name associated_function ->
    {{ k closure ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive
        (Primitive.GetAssociatedFunction ty name generic_tys) k ⇓
        output_to_value
    }}
  | CallPrimitiveGetTraitMethod
      (trait_name : string) (self_ty : Ty.t) (trait_tys : list Ty.t)
      (method_name : string) (generic_consts : list Value.t) (generic_tys : list Ty.t)
      (method : PolymorphicFunction.t)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (method generic_consts generic_tys)) in
    IsTraitMethod.t trait_name self_ty trait_tys method_name method ->
    {{ k closure ⇓ output_to_value }} ->
    {{ LowM.CallPrimitive
        (Primitive.GetTraitMethod
          trait_name
          self_ty
          trait_tys
          method_name
          generic_tys)
        k ⇓
        output_to_value
    }}
  | CallClosure {Output' : Set}
      (output_to_value' : Output' -> Value.t + Exception.t)
      (f : list Value.t -> M) (args : list Value.t)
      (k : Value.t + Exception.t -> M) :
    let closure := Value.Closure (existS (_, _) f) in
    {{ f args ⇓ output_to_value' }} ->
    (forall (value_inter : Output'),
      {{ k (output_to_value' value_inter) ⇓ output_to_value }}
    ) ->
    {{ LowM.CallClosure closure args k ⇓ output_to_value }}
  | Let {Output' : Set}
      (output_to_value' : Output' -> Value.t + Exception.t)
      (e : M) (k : Value.t + Exception.t -> M) :
    {{ e ⇓ output_to_value' }} ->
    (forall (value_inter : Output'),
      {{ k (output_to_value' value_inter) ⇓ output_to_value }}
    ) ->
    {{ LowM.Let e k ⇓ output_to_value }}
  | Rewrite (e e' : M) :
    e = e' ->
    {{ e' ⇓ output_to_value }} ->
    {{ e ⇓ output_to_value }}

  where "{{ e ⇓ output_to_value }}" :=
    (t output_to_value e).
End Run.

Import Run.

(** This lemma is convenient to handle the case of sub-pointers. We even have a dedicated tactic
    using it (defined below). Using the tactic is the recommended way. *)
Definition run_sub_pointer {kind : Pointer.Kind.t} {Output A Sub_A : Set}
    {IsLinkA : Link A} {IsLinkSub_A : Link Sub_A}
    {runner : SubPointer.Runner.t A Sub_A}
    (H_runner : SubPointer.Runner.Valid.t runner)
    (ref : Ref.t kind A) (pointer : Pointer.t Value.t)
    (k : Value.t -> M)
    (output_to_value : Output -> Value.t + Exception.t)
    (H_pointer : pointer = Ref.to_pointer ref)
    (H_k : forall (sub_ref : Ref.t kind Sub_A),
      let sub_pointer := Ref.to_pointer sub_ref in
      {{ k (Value.Pointer sub_pointer) ⇓ output_to_value }}
    ) :
  {{
    LowM.CallPrimitive (Primitive.GetSubPointer pointer runner.(SubPointer.Runner.index)) k ⇓
    output_to_value
  }}.
Proof.
  intros.
  eapply Run.CallPrimitiveGetSubPointer;
    try apply H_pointer;
    try apply H_runner;
    try apply H_k.
Defined.

Module Primitive.
  (** These primitives are equivalent to the ones in the generated code, except that we are now
      with types. We have also removed the primitives related to name/trait resolution, as this is
      now done. *)
  Inductive t : Set -> Set :=
  | StateAlloc (kind : Pointer.Kind.t) {A : Set} `{Link A} (value : A) : t (Ref.t kind A)
  | StateRead {kind : Pointer.Kind.t} {A : Set} `{Link A} (ref : Ref.t kind A) : t A
  | StateWrite {kind : Pointer.Kind.t} {A : Set} `{Link A} (ref : Ref.t kind A) (value : A) : t unit
  | GetSubPointer {kind : Pointer.Kind.t} {A Sub_A : Set} `{Link A} `{Link Sub_A}
    (ref : Ref.t kind A) (runner : SubPointer.Runner.t A Sub_A) :
    t (Ref.t kind Sub_A).
End Primitive.

Module LowM.
  (** The typed version of the [LowM.t] monad used in the generated code. We might need to use a
      co-inductive definition instead at some point. *)
  Inductive t (Output : Set) : Set :=
  | Pure (value : Output)
  | CallPrimitive {A : Set} (primitive : Primitive.t A) (k : A -> t Output)
  | Let {A : Set} (e : t A) (k : A -> t Output)
  | Loop {A : Set} (body : t A) (k : A -> t Output).
  Arguments Pure {_}.
  Arguments CallPrimitive {_ _}.
  Arguments Let {_ _}.
  Arguments Loop {_ _}.
End LowM.

(* We do not define an equivalent of [M] as the resulting term is generated, so we are not
   interested into having syntactic sugar for the error monad. *)

(** With this function we generate an expression in [LowM.t Output] that is equivalent to the
    input [e] expression, following the proof of equivalence provided in [run]. *)
Fixpoint evaluate {Output : Set}
  {e : M} {output_to_value : Output -> Value.t + Exception.t}
  (run : {{ e ⇓ output_to_value }}) :
  LowM.t Output.
Proof.
  destruct run.
  { (* Pure *)
    exact (LowM.Pure output).
  }
  { (* Alloc *)
    apply (LowM.CallPrimitive (Primitive.StateAlloc kind value)).
    intros ref_core.
    eapply evaluate.
    match goal with
    | H : forall _, _ |- _ => apply (H ref_core)
    end.
  }
  { (* AllocImmediate *)
    exact (evaluate _ _ _ run).
  }
  { (* Read *)
    apply (LowM.CallPrimitive (Primitive.StateRead ref)).
    intros value.
    eapply evaluate.
    match goal with
    | H : forall _, _ |- _ => apply (H value)
    end.
  }
  { (* ReadImmediate *)
    exact (evaluate _ _ _ run).
  }
  { (* Write *)
    apply (LowM.CallPrimitive (Primitive.StateWrite ref value)).
    intros _.
    exact (evaluate _ _ _ run).
  }
  { (* SubPointer *)
    apply (LowM.CallPrimitive (Primitive.GetSubPointer ref runner)).
    intros sub_ref.
    eapply evaluate.
    match goal with
    | H : forall _, _ |- _ => apply (H sub_ref)
    end.
  }
  { (* CallPrimitiveGetFunction *)
    exact (evaluate _ _ _ run).
  }
  { (* CallPrimitiveGetAssociatedFunction *)
    exact (evaluate _ _ _ run).
  }
  { (* CallPrimitiveGetTraitMethod *)
    exact (evaluate _ _ _ run).
  }
  { (* CallClosure *)
    eapply LowM.Let. {
      exact (evaluate _ _ _ run).
    }
    intros output'; eapply evaluate.
    match goal with
    | H : forall _ : Output', _ |- _ => apply (H output')
    end.
  }
  { (* Let *)
    eapply LowM.Let. {
      exact (evaluate _ _ _ run).
    }
    intros output'; eapply evaluate.
    match goal with
    | H : forall _ : Output', _ |- _ => apply (H output')
    end.
  }
  { (* Rewrite *)
    exact (evaluate _ _ _ run).
  }
Defined.

(*
Ltac run_symbolic_state_alloc :=
  (
    (* We hope the allocated value to be in a form that is already the image of a [φ] conversion. *)
    with_strategy opaque [φ] cbn;
    match goal with
    | |-
      {{
        CoqOfRust.M.LowM.CallPrimitive
          (CoqOfRust.M.Primitive.StateAlloc (φ (A := ?B) _)) _ ⇓
        _
      }} =>
        eapply Run.CallPrimitiveStateAlloc with (A := B);
        [try reflexivity |];
        intros
    end
  ) || (
    (* An important case is the allocation of the unit value *)
    eapply Run.CallPrimitiveStateAlloc with (value := tt); [reflexivity |];
    intros
  ).

Ltac run_symbolic_state_read :=
  cbn;
  eapply Run.CallPrimitiveStateRead; [reflexivity |];
  intros.

Ltac run_symbolic_state_write :=
  cbn;
  eapply Run.CallPrimitiveStateWrite; [reflexivity | reflexivity |];
  intros.

Ltac run_symbolic_one_step :=
  match goal with
  | |- {{ _ ⇓ _ }} =>
    (eapply Run.Pure; try reflexivity) ||
    run_symbolic_state_alloc ||
    run_symbolic_state_read ||
    run_symbolic_state_write
  end.

(** We should use this tactic instead of the ones above, as this one calls all the others. *)
Ltac run_symbolic :=
  repeat run_symbolic_one_step.

(** For the specific case of sub-pointers, we still do it by hand by providing the corresponding
    validity statement for the index that we access. *)
Ltac run_sub_pointer sub_pointer_is_valid :=
  cbn; eapply (run_sub_pointer sub_pointer_is_valid); [reflexivity|]; intros.

Module Function.
  Record t (Args Output : Set)
      (args_to_value : Args -> list Value.t)
      (output_to_value : Output -> Value.t + Exception.t) :
      Set := {
    f : list Value.t -> M;
    run_f : forall (args : Args),
      {{ f (args_to_value args) ⇓ output_to_value }};
  }.
End Function.

Module Function2.
  Record t (A1 A2 Output : Set)
      `{Link A1} `{Link A2}
      (output_to_value : Output -> Value.t + Exception.t) :
      Set := {
    f : list Value.t -> M;
    run_f : forall (a1 : A1) (a2 : A2),
      {{ f [ φ a1; φ a2 ] ⇓ output_to_value }};
  }.
End Function2.
*)
