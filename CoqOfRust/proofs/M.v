Require Import Coq.Strings.String.
Require Import CoqOfRust.M.
Require Import simulations.M.

Import List.ListNotations.

Local Open Scope list.
Local Open Scope type.

Module State.
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

(* Module IsRead.
  Inductive t `{State.Trait} (state : State) : Pointer.t Value.t -> Value.t -> Prop :=
  | Immediate (value : Value.t) :
    t state (Pointer.Immediate value) value
  | Mutable
      {A : Set} {pointer_to_value : A -> Value.t} address path big_to_value projection injection
      (value : State.get_Set address)
      (sub_value : A) :
    let mutable :=
      Pointer.Mutable.Make
        (Value := Value.t) (A := A) (to_value := pointer_to_value) (Address := Address)
        (Big_A := State.get_Set address)
        address
        path
        big_to_value
        projection
        injection in
    State.read address state = Some value ->
    projection value = Some sub_value ->
    t state (Pointer.Mutable mutable) (pointer_to_value sub_value).
End IsRead.

Module HasRead.
  Definition t `{State.Trait} {A : Set}
      (state : State) (pointer : Pointer.t Value.t) (to_value : A -> Value.t) :
      Set :=
    { a : A @ IsRead.t state pointer (to_value a)}.
End HasRead.

Module Run.
  Reserved Notation "{{ env , state | e ⇓ to_value | P_state }}".

  Inductive t `{State.Trait} {A : Set} (env : Value.t) (state : State)
      (to_value : A -> Value.t + Exception.t) (P_state : State -> Prop) :
      M -> Set :=
  | Pure
      (result : A)
      (result' : Value.t + Exception.t) :
    result' = to_value result ->
    P_state state ->
    {{ env, state | LowM.Pure result' ⇓ to_value | P_state }}
  | CallPrimitiveStateAllocImmediate
      (v : Value.t)
      (k : Value.t -> M) :
    {{ env, state |
      k (Value.Pointer (Pointer.Immediate v)) ⇓ to_value
    | P_state }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateAlloc v) k ⇓ to_value
    | P_state }}
  | CallPrimitiveStateAllocMutable
      (address : Address)
      (value : State.get_Set address)
      (value' : Value.t)
      (pointer_to_value : State.get_Set address -> Value.t)
      (state_inter : State)
      (k : Value.t -> M) :
    let r := Value.Pointer (Pointer.mutable address pointer_to_value) in
    value' = pointer_to_value value ->
    State.read address state = None ->
    State.alloc_write address state value = Some state_inter ->
    {{ env, state_inter | k r ⇓ to_value | P_state }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateAlloc value') k ⇓ to_value
    | P_state }}
  | CallPrimitiveStateRead
      (pointer : Pointer.t Value.t)
      (value : Value.t)
      (k : Value.t -> M) :
    IsRead.t state pointer value ->
    {{ env, state |
      k value ⇓
      to_value
    | P_state }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateRead pointer) k ⇓
      to_value
    | P_state }}
  | CallPrimitiveStateWrite
      {A : Set} {pointer_to_value : A -> Value.t} address path big_to_value projection injection
      (value : A) (value' : Value.t)
      (big_value new_big_value : State.get_Set address)
      (state_inter : State)
      (k : Value.t -> M) :
    let mutable :=
      Pointer.Mutable.Make
        (Value := Value.t) (A := A) (to_value := pointer_to_value) (Address := Address)
        (Big_A := State.get_Set address)
        address
        path
        big_to_value
        projection
        injection in
    value' = pointer_to_value value ->
    State.read address state = Some big_value ->
    injection big_value value = Some new_big_value ->
    State.alloc_write address state new_big_value = Some state_inter ->
    {{ env, state_inter | k (Value.Tuple []) ⇓ to_value | P_state }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateWrite mutable value') k ⇓
      to_value
    | P_state }}
  | CallPrimitiveGetSubPointer {A Sub_A : Set} {pointer_to_value : A -> Value.t}
      (mutable : Pointer.Mutable.t Value.t pointer_to_value)
      index sub_projection sub_injection sub_to_value
      (k : Value.t -> M) :
    (* Communtativity of the read *)
    (forall (a : A),
      Option.map (sub_projection a) sub_to_value =
      Value.read_path (pointer_to_value a) [index]
    ) ->
    (* Communtativity of the write *)
    (forall (a : A) (sub_a : Sub_A),
      Option.map (sub_injection a sub_a) pointer_to_value =
      Value.write_value (pointer_to_value a) [index] (sub_to_value sub_a)
    ) ->
    {{ env, state |
      k (Value.Pointer (Pointer.Mutable (Pointer.Mutable.get_sub
        mutable index sub_projection sub_injection sub_to_value
      ))) ⇓
      to_value
    | P_state }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.GetSubPointer mutable index) k ⇓
      to_value
    | P_state }}
  | CallPrimitiveEnvRead
      (k : Value.t -> M) :
    {{ env, state | k env ⇓ to_value | P_state }} ->
    {{ env, state |
      LowM.CallPrimitive Primitive.EnvRead k ⇓ to_value
    | P_state }}
  | CallPrimitiveGetFunction
      (name : string) (generic_tys : list Ty.t)
      (function : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (function generic_tys)) in
    M.IsFunction name function ->
    {{ env, state | k closure ⇓ to_value | P_state }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.GetFunction name generic_tys) k ⇓
      to_value
    | P_state }}
  | CallPrimitiveGetAssociatedFunction
      (ty : Ty.t) (name : string) (generic_tys : list Ty.t)
      (associated_function : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (associated_function generic_tys)) in
    M.IsAssociatedFunction ty name associated_function ->
    {{ env, state | k closure ⇓ to_value | P_state }} ->
    {{ env, state |
      LowM.CallPrimitive
        (Primitive.GetAssociatedFunction ty name generic_tys) k ⇓
        to_value
    | P_state }}
  | CallPrimitiveGetTraitMethod
      (trait_name : string) (self_ty : Ty.t) (trait_tys : list Ty.t)
      (method_name : string) (generic_tys : list Ty.t)
      (method : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure := Value.Closure (existS (_, _) (method generic_tys)) in
    IsTraitMethod.t trait_name self_ty trait_tys method_name method ->
    {{ env, state | k closure ⇓ to_value | P_state }} ->
    {{ env, state |
      LowM.CallPrimitive
        (Primitive.GetTraitMethod
          trait_name
          self_ty
          trait_tys
          method_name
          generic_tys)
        k ⇓
        to_value
    | P_state }}
  | CallClosure {A_inter : Set}
      (to_value_inter : A_inter -> Value.t + Exception.t) (P_state_inter : State -> Prop)
      (f : list Value.t -> M) (args : list Value.t)
      (k : Value.t + Exception.t -> M) :
    let closure := Value.Closure (existS (_, _) f) in
    {{ env, state | f args ⇓ to_value_inter | P_state_inter }} ->
    (forall (value_inter : A_inter) (state_inter : State),
      P_state_inter state_inter ->
      {{ env, state_inter | k (to_value_inter value_inter) ⇓ to_value | P_state }}
    ) ->
    {{ env, state | LowM.CallClosure closure args k ⇓ to_value | P_state }}
  | Let {A_inter : Set}
      (to_value_inter : A_inter -> Value.t + Exception.t) (P_state_inter : State -> Prop)
      (e : M) (k : Value.t + Exception.t -> M) :
    {{ env, state | e ⇓ to_value_inter | P_state_inter }} ->
    (forall (value_inter : A_inter) (state_inter : State),
      {{ env, state_inter | k (to_value_inter value_inter) ⇓ to_value | P_state }}
    ) ->
    {{ env, state | LowM.Let e k ⇓ to_value | P_state }}
  | Rewrite (e e' : M) :
    e = e' ->
    {{ env, state | e' ⇓ to_value | P_state }} ->
    {{ env, state | e ⇓ to_value | P_state }}

  where "{{ env , state | e ⇓ to_value | P_state }}" :=
    (t env state to_value P_state e).

  Notation "{{ '_' , state | e ⇓ to_value | P_state }}" :=
    (forall (env : Value.t),
      {{ env, state | e ⇓ to_value | P_state }}
    ).

  Notation "{{ '_' , '_' | e ⇓ to_value | '_' }}" :=
    (forall (State Address : Set) `(State.Trait State Address) (state : State),
      {{ _, state | e ⇓ to_value | fun state' => state' = state }}
    ).
End Run.

Import Run.

Fixpoint evaluate `{State.Trait} {A : Set}
    {env : Value.t} {state : State}
    {e : M} {to_value : A -> Value.t + Exception.t}
    {P_state : State -> Prop}
    (run : {{ env, state | e ⇓ to_value | P_state }}) :
  A * { state : State | P_state state }.
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
  { destruct (evaluate _ _ _ _ _ _ _ _ _ run) as [value_inter [state_inter H_state_inter]].
    eapply evaluate.
    match goal with
    | H : forall _ _ _, _ |- _ => apply (H value_inter state_inter)
    end.
    exact H_state_inter.
  }
  { destruct (evaluate _ _ _ _ _ _ _ _ _ run) as [value_inter [state_inter H_state_inter]].
    eapply evaluate.
    match goal with
    | H : forall _ _, _ |- _ => apply (H value_inter state_inter)
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
      `{State.Trait} (env : Value.t) (state : State)
      (to_value : Result -> Value.t + Exception.t) (P_state : State -> Prop)
      (k : Value.t -> M)
      (index : Pointer.Index.t)
      (H_index : index = runner.(SubPointer.Runner.index)) :
    {{ env, state |
      k (Value.Pointer (Pointer.Mutable (SubPointer.get_sub mutable runner))) ⇓
      to_value
    | P_state }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.GetSubPointer mutable index) k ⇓
      to_value
    | P_state }}.
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
  | |- Run.t ?env ?state ?to_value ?P_state
      (LowM.CallPrimitive (Primitive.StateWrite (
        Pointer.Mutable.Make ?address ?path ?big_to_value ?projection ?injection
      ) ?value') ?k) =>
    let H := fresh "H" in
    epose proof (H :=
      Run.CallPrimitiveStateWrite
        env state to_value P_state address path big_to_value projection injection _
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
End StatelessFunction. *)
