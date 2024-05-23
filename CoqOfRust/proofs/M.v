Require Import Coq.Strings.String.
Require Import CoqOfRust.M.
Require Import CoqOfRust.simulations.M.

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

Definition IsTraitMethod
    (trait_name : string)
    (self_ty : Ty.t)
    (trait_tys : list Ty.t)
    (method_name : string)
    (method : list Ty.t -> list Value.t -> M) :
    Prop :=
  exists (instance : Instance.t),
  M.IsTraitInstance
    trait_name
    self_ty
    trait_tys
    instance /\
  List.assoc instance method_name = Some (InstanceField.Method method).

Module Run.
  Reserved Notation "{{ env , env_to_value , state | e ⇓ to_value | P_state }}".

  Inductive t `{State.Trait} {Env A : Set} (env : Env) (env_to_value : Env -> Value.t)
      (state : State)
      (to_value : A -> Value.t + Exception.t) (P_state : State -> Prop) :
      M -> Set :=
  | Pure
      (result : A)
      (result' : Value.t + Exception.t) :
    result' = to_value result ->
    P_state state ->
    {{ env, env_to_value, state | LowM.Pure result' ⇓ to_value | P_state }}
  | CallPrimitiveStateAllocImmediate
      (v : Value.t)
      (k : Value.t -> M) :
    {{ env, env_to_value, state |
      k (Value.Pointer (Pointer.Immediate v)) ⇓ to_value
    | P_state }} ->
    {{ env, env_to_value, state |
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
    {{ env, env_to_value, state_inter | k r ⇓ to_value | P_state }} ->
    {{ env, env_to_value, state |
      LowM.CallPrimitive (Primitive.StateAlloc value') k ⇓ to_value
    | P_state }}
  | CallPrimitiveStateRead
      {A : Set} {pointer_to_value : A -> Value.t} address path big_to_value projection injection
      (value : State.get_Set address)
      (sub_value : A)
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
    State.read address state = Some value ->
    projection value = Some sub_value ->
    {{ env, env_to_value, state |
      k (pointer_to_value sub_value) ⇓
      to_value
    | P_state }} ->
    {{ env, env_to_value, state |
      LowM.CallPrimitive (Primitive.StateRead mutable) k ⇓
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
    {{ env, env_to_value, state_inter | k (Value.Tuple []) ⇓ to_value | P_state }} ->
    {{ env, env_to_value, state |
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
    {{ env, env_to_value, state |
      k (Value.Pointer (Pointer.Mutable (Pointer.Mutable.get_sub
        mutable index sub_projection sub_injection sub_to_value
      ))) ⇓
      to_value
    | P_state }} ->
    {{ env, env_to_value, state |
      LowM.CallPrimitive (Primitive.GetSubPointer mutable index) k ⇓
      to_value
    | P_state }}
  | CallPrimitiveEnvRead
      (k : Value.t -> M) :
    {{ env, env_to_value, state | k (env_to_value env) ⇓ to_value | P_state }} ->
    {{ env, env_to_value, state |
      LowM.CallPrimitive Primitive.EnvRead k ⇓ to_value
    | P_state }}
  | CallPrimitiveGetFunction
      (name : string) (generic_tys : list Ty.t)
      (function : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure :=
      Value.Closure (existS (Value.t, M) (function generic_tys)) in
    M.IsFunction name function ->
    {{ env, env_to_value, state | k closure ⇓ to_value | P_state }} ->
    {{ env, env_to_value, state |
      LowM.CallPrimitive (Primitive.GetFunction name generic_tys) k ⇓
      to_value
    | P_state }}
  | CallPrimitiveGetAssociatedFunction
      (ty : Ty.t) (name : string) (generic_tys : list Ty.t)
      (associated_function : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure :=
      Value.Closure (existS (Value.t, M) (associated_function generic_tys)) in
    M.IsAssociatedFunction ty name associated_function ->
    {{ env, env_to_value, state | k closure ⇓ to_value | P_state }} ->
    {{ env, env_to_value, state |
      LowM.CallPrimitive
        (Primitive.GetAssociatedFunction ty name generic_tys) k ⇓
        to_value
    | P_state }}
  | CallPrimitiveGetTraitMethod
      (trait_name : string) (self_ty : Ty.t) (trait_tys : list Ty.t)
      (method_name : string) (generic_tys : list Ty.t)
      (method : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure :=
      Value.Closure (existS (Value.t, M) (method generic_tys)) in
    IsTraitMethod trait_name self_ty trait_tys method_name method ->
    {{ env, env_to_value, state | k closure ⇓ to_value | P_state }} ->
    {{ env, env_to_value, state |
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
    let closure := Value.Closure (existS (Value.t, M) f) in
    {{ env, env_to_value, state | f args ⇓ to_value_inter | P_state_inter }} ->
    (forall (value_inter : A_inter) (state_inter : State),
      P_state_inter state_inter ->
      {{ env, env_to_value, state_inter | k (to_value_inter value_inter) ⇓ to_value | P_state }}
    ) ->
    {{ env, env_to_value, state | LowM.CallClosure closure args k ⇓ to_value | P_state }}

  where "{{ env , env_to_value , state | e ⇓ to_value | P_state }}" :=
    (t env env_to_value state to_value P_state e).

  Definition pure {A : Set} (e : M) (to_value : A -> Value.t + Exception.t) : Set :=
    forall
      (State Address : Set) `(State.Trait State Address)
      (Env : Set) (env : Env) (env_to_value : Env -> Value.t)
      (state : State),
    {{ env, env_to_value, state |
      e ⇓ to_value
    | fun state' => state' = state }}.
End Run.

Import Run.

Fixpoint evaluate `{State.Trait} {Env A : Set}
    {env : Env} {env_to_value : Env -> Value.t} {state : State}
    {e : M} {to_value : A -> Value.t + Exception.t}
    {P_state : State -> Prop}
    (run : {{ env, env_to_value, state | e ⇓ to_value | P_state }}) :
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
  { destruct (evaluate _ _ _ _ _ _ _ _ _ _ _ run) as [value_inter [state_inter H_state_inter]].
    eapply evaluate.
    match goal with
    | H : forall _ _ _, _ |- _ => apply (H value_inter)
    end.
    exact H_state_inter.
  }
Defined.

Module SubPointer.
  Module Runner.
    Module Valid.
      Inductive t {A Sub_A : Set} `{ToValue A} `{ToValue Sub_A} :
          SubPointer.Runner.t A Sub_A -> Set :=
      | Intro
          (index : Pointer.Index.t)
          (projection : A -> option Sub_A)
          (injection : A -> Sub_A -> option A) :
        (* read equivalence *)
        (forall (a : A),
          Option.map (projection a) φ =
          Value.read_path (φ a) [index]
        ) ->
        (* write equivalence *)
        (forall (a : A) (sub_a : Sub_A),
          Option.map (injection a sub_a) φ =
          Value.write_value (φ a) [index] (φ sub_a)
        ) ->
        t {|
          SubPointer.Runner.index := index;
          SubPointer.Runner.projection := projection;
          SubPointer.Runner.injection := injection;
        |}.
    End Valid.
  End Runner.

  Import Run.

  Definition run
      {Result : Set} {A Sub_A : Set} `{ToValue A} `{ToValue Sub_A}
      {runner : SubPointer.Runner.t A Sub_A}
      (H_runner : Runner.Valid.t runner)
      (mutable : Pointer.Mutable.t (A := A) Value.t φ)
      `{State.Trait} {Env : Set} (env : Env) (env_to_value : Env -> Value.t) (state : State)
      (to_value : Result -> Value.t + Exception.t) (P_state : State -> Prop)
      (k : Value.t -> M)
      (index : Pointer.Index.t) :
    index = runner.(SubPointer.Runner.index) ->
    {{ env, env_to_value, state |
      k (Value.Pointer (Pointer.Mutable (SubPointer.get_sub mutable runner))) ⇓
      to_value
    | P_state }} ->
    {{ env, env_to_value, state |
      LowM.CallPrimitive (Primitive.GetSubPointer mutable index) k ⇓
      to_value
    | P_state }}.
  Proof.
    intros.
    destruct H_runner.
    eapply Run.CallPrimitiveGetSubPointer; sfirstorder.
  Defined.
End SubPointer.

(** Simplify the usual case of read of immediate value. *)
Lemma read_of_immediate (v : Value.t) :
  M.read (Value.Pointer (Pointer.Immediate v)) =
  M.pure v.
Proof.
  reflexivity.
Qed.

Ltac run_symbolic_state_read :=
  match goal with
  | |- Run.t _ _ _ _ _ (LowM.CallPrimitive (Primitive.StateRead (
      Pointer.Mutable.Make ?address _ _ _ _
    )) _) =>
    let H := fresh "H" in
    epose proof (H := Run.CallPrimitiveStateRead _ _ _ _ _ address);
    eapply H; [reflexivity | reflexivity |];
    clear H
  end.

Ltac run_symbolic_state_write :=
  match goal with
  | |- Run.t ?env ?env_to_value ?state ?to_value ?P_state
      (LowM.CallPrimitive (Primitive.StateWrite (
        Pointer.Mutable.Make ?address ?path ?big_to_value ?projection ?injection
      ) ?value') ?k) =>
    let H := fresh "H" in
    epose proof (H :=
      Run.CallPrimitiveStateWrite
        env env_to_value state to_value P_state address path big_to_value projection injection _
        value' _ _ _ k
    );
    apply H; try reflexivity;
    clear H
  end.

Ltac run_symbolic_one_step :=
  match goal with
  | |- Run.t _ _ _ _ _ _ =>
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
