Require Import Coq.Strings.String.
Require Import CoqOfRust.M.
Require Import simulations.M.

Import List.ListNotations.

Local Open Scope list.
Local Open Scope type.

(* Module State.
  Class Trait (State Address : Set) : Type := {
    get_Set (a : Address) : Set;
    read (a : Address) : State -> option (get_Set a);
    alloc_write (a : Address) : State -> get_Set a -> option State;
  }.

  Module Valid.
    (** A valid state should behave as map from address to optional values
        of the type given by the address. A value is [None] while not
        allocated, and [Some] once allocated. It is impossible to free
        allocated values. *)
    Record t `(Trait) : Prop := {
      (* [alloc_write] can only fail on new cells *)
      not_allocated (a : Address) (s : State) (v : get_Set a) :
        match alloc_write a s v with
        | Some _ => True
        | None => read a s = None
        end;
      same (a : Address) (s : State) (v : get_Set a) :
        match alloc_write a s v with
        | Some s => read a s = Some v
        | None => True
        end;
      different (a1 a2 : Address) (s : State) (v2 : get_Set a2) :
        a1 <> a2 ->
        match alloc_write a2 s v2 with
        | Some s' => read a1 s' = read a1 s
        | None => True
        end;
        }.
  End Valid.
End State.

Module Stack.
  Module State.
    Inductive t : list Set -> Set :=
    | Nil : t []
    | Cons {A : Set} {As : list Set} (x : A) (xs : t As) : t (A :: As).
  End State.

  Module Address.
    Definition t : Set := nat.
  End Address.

  Definition get_Set (domain : list Set) (address : Address.t) : Set :=
    List.nth address domain Empty_set.

  Fixpoint read {domain : list Set} (address : Address.t) (state : State.t domain) :
      option (get_Set domain address) :=
    match state with
    | State.Nil => None
    | State.Cons x xs =>
      match address with
      | O => Some x
      | S address' => read address' xs
      end
    end.

  Fixpoint alloc_write {domain : list Set}
    (address : Address.t)
    (state : State.t domain)
    (value : get_Set domain address)
    {struct state} :
    option (State.t domain).
  Proof.
    destruct state as [| ? ? x xs].
    { destruct address, value. }
    { destruct address as [| address']; cbn in *.
      { exact (Some (State.Cons value xs)). }
      { destruct (alloc_write _ address' xs value) as [xs' |].
        { exact (Some (State.Cons x xs')). }
        { exact None. }
      }
    }
  Defined.

  Global Instance I {domain : list Set} : State.Trait (State.t domain) Address.t := {
    get_Set := get_Set domain;
    read := read;
    alloc_write := alloc_write;
  }.

  Definition alloc {A : Set} {domain : list Set} (state : State.t domain) (value : A)
End Stack. *)

Module IsTraitMethod.
  Inductive t
      (trait_name : string)
      (self_ty : Ty.t)
      (trait_tys : list Ty.t)
      (method_name : string) :
      (list Ty.t -> list Value.t -> M) -> Prop :=
  | Explicit (instance : Instance.t) (method : list Ty.t -> list Value.t -> M) :
    M.IsTraitInstance
      trait_name
      self_ty
      trait_tys
      instance ->
    List.assoc instance method_name = Some (InstanceField.Method method) ->
    t trait_name self_ty trait_tys method_name method
  | Implicit (instance : Instance.t) (method : Ty.t -> list Ty.t -> list Value.t -> M) :
    M.IsTraitInstance
      trait_name
      self_ty
      trait_tys
      instance ->
    List.assoc instance method_name = None ->
    M.IsProvidedMethod trait_name method_name method ->
    t trait_name self_ty trait_tys method_name (method self_ty).
End IsTraitMethod.

Module Stack.
  Definition t : Set :=
    list (option {A : Set @ A}).

  Definition read (stack : t) (address : nat) : option {A : Set @ A} :=
    match List.nth_error stack address with
    | Some (Some value) => Some value
    | Some None | None => None
    end.

  Fixpoint write {A : Set} (stack : t) (address : nat) (value : A) : t :=
    match stack, address with
    | None :: _, Datatypes.O => stack
    | Some _ :: stack, Datatypes.O => Some (existS A value) :: stack
    | start :: stack, Datatypes.S address => start :: write stack address value
    | [], _ => []
    end.

  Lemma read_length_eq {A : Set} (stack_start stack_end : t) :
    read (stack_start ++ stack_end) (List.length stack_start) =
    read stack_end 0.
  Proof.
    now induction stack_start.
  Qed.
End Stack.

Module HasReadWith.
  Inductive t {A : Set} (stack : Stack.t) (to_value : A -> Value.t) (value : A) :
      Pointer.t Value.t -> Prop :=
  | Immediate :
    t stack to_value value (Pointer.Immediate to_value value)
  | Mutable {Big_A : Set} address path big_to_value projection injection (big_value : Big_A) :
    let mutable :=
      Pointer.Mutable.Make
        (Value := Value.t) (A := A) (to_value := to_value)
        (Big_A := Big_A)
        address
        path
        big_to_value
        projection
        injection in
    Stack.read stack address = Some (existS _ big_value) ->
    projection big_value = Some value ->
    t stack to_value value (Pointer.Mutable mutable).
End HasReadWith.

Module HasRead.
  Definition t {A : Set}
      (stack : Stack.t)
      (pointer : Pointer.t Value.t)
      (to_value : A -> Value.t) :
      Set :=
    { value : A | HasReadWith.t stack to_value value pointer}.
End HasRead.

Module HasWriteWith.
  Inductive t {A : Set} {to_value : A -> Value.t} (stack : Stack.t) (value : A) :
      Pointer.Mutable.t Value.t to_value -> Stack.t -> Prop :=
  | Mutable {Big_A : Set} address path big_to_value projection injection (big_value : Big_A) :
    let mutable :=
      Pointer.Mutable.Make
        (Value := Value.t) (A := A) (to_value := to_value)
        (Big_A := Big_A)
        address
        path
        big_to_value
        projection
        injection in
    let stack' := Stack.write stack address value in
    HasRead.t stack' (Pointer.Mutable mutable) to_value ->
    t stack value mutable stack'.
End HasWriteWith.

Module HasWrite.
  Definition t {A : Set} {to_value : A -> Value.t}
      (stack : Stack.t)
      (value : A)
      (mutable : Pointer.Mutable.t Value.t to_value) :
      Set :=
    { stack' : Stack.t | HasWriteWith.t stack value mutable stack' }.
End HasWrite.

Module Run.
  Reserved Notation "{{ stack | e ⇓ to_value }}".

  Inductive t {Output : Set} (stack : Stack.t) (output_to_value : Output -> Value.t + Exception.t) :
      M -> Set :=
  | Pure
      (output : Output)
      (output' : Value.t + Exception.t) :
    output' = output_to_value output ->
    {{ stack | LowM.Pure output' ⇓ output_to_value }}
  | CallPrimitiveStateAllocImmediate {A : Set}
      (value : A) (value' : Value.t)
      (to_value : A -> Value.t)
      (k : Value.t -> M) :
    value' = to_value value ->
    {{ stack | k (Value.Pointer (Pointer.Immediate to_value value)) ⇓ output_to_value }} ->
    {{ stack | LowM.CallPrimitive (Primitive.StateAlloc value') k ⇓ output_to_value }}
  | CallPrimitiveStateAllocMutable {A : Set}
      (value : A) (value' : Value.t)
      (to_value : A -> Value.t)
      (stack_inter : Stack.t)
      (k : Value.t -> M) :
    let address := List.length stack in
    let r := Value.Pointer (Pointer.mutable address to_value) in
    value' = to_value value ->
    let stack_inter : Stack.t := stack ++ [Some (existS _ value)] in
    {{ stack_inter | k r ⇓ output_to_value }} ->
    {{ stack | LowM.CallPrimitive (Primitive.StateAlloc value') k ⇓ output_to_value }}
  | CallPrimitiveStateRead {A : Set}
      (pointer : Pointer.t Value.t)
      (value : A) (value' : Value.t)
      (to_value : A -> Value.t)
      (k : Value.t -> M) :
    value' = to_value value ->
    HasReadWith.t stack to_value value pointer ->
    {{ stack | k value' ⇓ output_to_value }} ->
    {{ stack | LowM.CallPrimitive (Primitive.StateRead pointer) k ⇓ output_to_value }}
  | CallPrimitiveStateWrite
      {A : Set}
      (value : A) (value' : Value.t)
      (to_value : A -> Value.t)
      (mutable : Pointer.Mutable.t Value.t to_value)
      (stack_inter : Stack.t)
      (k : Value.t -> M) :
    value' = to_value value ->
    HasWriteWith.t stack value mutable stack_inter ->
    {{ stack_inter | k (Value.Tuple []) ⇓ output_to_value }} ->
    {{ stack | LowM.CallPrimitive (Primitive.StateWrite mutable value') k ⇓ output_to_value }}
  | CallPrimitiveGetSubPointer {A Sub_A : Set} {to_value : A -> Value.t}
      (mutable : Pointer.Mutable.t Value.t to_value)
      index sub_projection sub_injection sub_to_value
      (k : Value.t -> M) :
    (* Communtativity of the read *)
    (forall (a : A),
      Option.map (sub_projection a) sub_to_value =
      Value.read_path (to_value a) [index]
    ) ->
    (* Communtativity of the write *)
    (forall (a : A) (sub_a : Sub_A),
      Option.map (sub_injection a sub_a) to_value =
      Value.write_value (to_value a) [index] (sub_to_value sub_a)
    ) ->
    {{ stack |
      k (Value.Pointer (Pointer.Mutable (Pointer.Mutable.get_sub
        mutable index sub_projection sub_injection sub_to_value
      ))) ⇓
      output_to_value
    }} ->
    {{ stack | LowM.CallPrimitive (Primitive.GetSubPointer mutable index) k ⇓ output_to_value }}
  | CallPrimitiveGetFunction
      (name : string) (generic_tys : list Ty.t)
      (function : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (function generic_tys)) in
    M.IsFunction name function ->
    {{ stack | k closure ⇓ output_to_value }} ->
    {{ stack | LowM.CallPrimitive (Primitive.GetFunction name generic_tys) k ⇓ output_to_value }}
  | CallPrimitiveGetAssociatedFunction
      (ty : Ty.t) (name : string) (generic_tys : list Ty.t)
      (associated_function : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (associated_function generic_tys)) in
    M.IsAssociatedFunction ty name associated_function ->
    {{ stack | k closure ⇓ output_to_value }} ->
    {{ stack |
      LowM.CallPrimitive
        (Primitive.GetAssociatedFunction ty name generic_tys) k ⇓
      output_to_value
    }}
  | CallPrimitiveGetTraitMethod
      (trait_name : string) (self_ty : Ty.t) (trait_tys : list Ty.t)
      (method_name : string) (generic_tys : list Ty.t)
      (method : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (method generic_tys)) in
    IsTraitMethod.t trait_name self_ty trait_tys method_name method ->
    {{ stack | k closure ⇓ output_to_value }} ->
    {{ stack |
      LowM.CallPrimitive
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
    {{ stack | f args ⇓ output_to_value' }} ->
    (forall (output' : Output') (stack' : Stack.t),
      (* We do not de-allocate what was already there on the stack *)
      (forall {A : Set} {to_value : A -> Value.t}
        (value : A) (mutable : Pointer.Mutable.t Value.t to_value),
        HasWrite.t stack value mutable ->
        HasWrite.t stack' value mutable
      ) ->
      {{ stack' | k (output_to_value' output') ⇓ output_to_value }}
    ) ->
    {{ stack | LowM.CallClosure closure args k ⇓ output_to_value }}
  | Rewrite (e e' : M) :
    e = e' ->
    {{ stack | e' ⇓ output_to_value }} ->
    {{ stack | e ⇓ output_to_value }}

  where "{{ stack | e ⇓ to_value }}" :=
    (t stack to_value e).

  Notation "{{ '_' | e ⇓ to_value }}" :=
    (forall (State Address : Set) `(State.Trait State Address) (stack : Stack.t),
      {{ stack | e ⇓ to_value }}
    ).
End Run.

Import Run.

Fixpoint evaluate `{State.Trait} {A : Set}
    {env : Value.t} {stack : State}
    {e : M} {to_value : A -> Value.t + Exception.t}
    (run : {{ stack | e ⇓ to_value }}) :
  A * State.
Proof.
  destruct run.
  { split.
    { exact result. }
    { eexists.
      match goal with
      | H : P_state _ |- _ => exact H
      end.
    }
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { eapply evaluate.
    exact run.
  }
  { destruct (evaluate _ _ _ _ _ _ _ _ _ run) as [value_inter [stack_inter H_state_inter]].
    eapply evaluate.
    match goal with
    | H : forall _ _ _, _ |- _ => apply (H value_inter stack_inter)
    end.
    exact H_state_inter.
  }
  { destruct (evaluate _ _ _ _ _ _ _ _ _ run) as [value_inter [stack_inter H_state_inter]].
    eapply evaluate.
    match goal with
    | H : forall _ _, _ |- _ => apply (H value_inter stack_inter)
    end.
  }
  { eapply evaluate.
    exact run.
  }
Defined.

Module SubPointer.
  Module Runner.
    Module Valid.
      Inductive t {A Sub_A : Set} `{ToValue A} `{ToValue Sub_A}
          (runner : SubPointer.Runner.t A Sub_A) :
        Prop :=
      | Intro :
        (* read equivalence *)
        (forall (a : A),
          Option.map (runner.(SubPointer.Runner.projection) a) φ =
          Value.read_path (φ a) [runner.(SubPointer.Runner.index)]
        ) ->
        (* write equivalence *)
        (forall (a : A) (sub_a : Sub_A),
          Option.map (runner.(SubPointer.Runner.injection) a sub_a) φ =
          Value.write_value (φ a) [runner.(SubPointer.Runner.index)] (φ sub_a)
        ) ->
        t runner.
    End Valid.
  End Runner.

  Import Run.

  Definition run
      {Result : Set} {A Sub_A : Set} `{ToValue A} `{ToValue Sub_A}
      {runner : SubPointer.Runner.t A Sub_A}
      (H_runner : Runner.Valid.t runner)
      (mutable : Pointer.Mutable.t (A := A) Value.t φ)
      `{State.Trait} (env : Value.t) (stack : State)
      (to_value : Result -> Value.t + Exception.t) (P_state : State -> Prop)
      (k : Value.t -> M)
      (index : Pointer.Index.t)
      (H_index : index = runner.(SubPointer.Runner.index)) :
    {{ stack |
      k (Value.Pointer (Pointer.Mutable (SubPointer.get_sub mutable runner))) ⇓
      to_value }} ->
    {{ stack |
      LowM.CallPrimitive (Primitive.GetSubPointer mutable index) k ⇓
      to_value }}.
  Proof.
    (* We are careful in this proof not to do `rewrite` on the expressions to avoid blocking
       the [evaluate] function. *)
    intros H_run.
    eapply Run.Rewrite. {
      rewrite H_index; reflexivity.
    }
    apply (Run.CallPrimitiveGetSubPointer
      _ _ _ _ _
      runner.(SubPointer.Runner.index)
      runner.(SubPointer.Runner.projection)
      runner.(SubPointer.Runner.injection)
      φ
    ); try apply H_run.
    all: sfirstorder.
  Defined.
End SubPointer.

Ltac run_symbolic_state_read :=
  eapply Run.CallPrimitiveStateRead; [
    match goal with
    | |- context [Pointer.Mutable.Make ?address] =>
      let H := fresh "H" in
      epose proof (H := IsRead.Mutable _ address);
      eapply H; reflexivity;
      clear H
    | _ => apply IsRead.Immediate
    end
  |].

Ltac run_symbolic_state_write :=
  match goal with
  | |- Run.t ?env ?stack ?to_value ?P_state
      (LowM.CallPrimitive (Primitive.StateWrite (
        Pointer.Mutable.Make ?address ?path ?big_to_value ?projection ?injection
      ) ?value') ?k) =>
    let H := fresh "H" in
    epose proof (H :=
      Run.CallPrimitiveStateWrite
        env stack to_value P_state address path big_to_value projection injection _
        value' _ _ _ k
    );
    apply H; try reflexivity;
    clear H
  end.

Ltac run_symbolic_one_step :=
  match goal with
  | |- Run.t _ _ _ _ _ =>
    (* We do not use [Run.CallClosure] and let the user use existing lemma
       for this kind of case. *)
    (eapply Run.Pure; trivial) ||
    apply Run.CallPrimitiveStateAllocImmediate ||
    apply Run.CallPrimitiveEnvRead ||
    run_symbolic_state_read ||
    run_symbolic_state_write
  end.

Ltac run_symbolic :=
  repeat (
    cbn ||
    run_symbolic_one_step
  ).

Module StatelessFunction.
  (** We describe a stateless function as its implementation together the ability to get a run in a
      stateless environment. *)
  Record t {Args Output : Set}
      {args_to_value : Args -> list Value.t} {output_to_value : Output -> Value.t} : 
      Set := {
    f : list Value.t -> M;
    run (args : Args) :
      {{ _, _ |
        f (args_to_value args) ⇓
        fun v => inl (output_to_value v)
      | _ }}
  }.
  Arguments t {_ _}.

  Global Instance IsToValue {Args Output : Set}
      (args_to_value : Args -> list Value.t) (output_to_value : Output -> Value.t) :
      ToValue (t args_to_value output_to_value) := {
    φ v := Value.Closure (existS (_, _) v.(f));
  }.
End StatelessFunction.
