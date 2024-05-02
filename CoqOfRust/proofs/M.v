Require Import Coq.Strings.String.
Require Import CoqOfRust.M.
Require CoqOfRust.simulations.M.

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
  Reserved Notation "{{ env , state | e ⇓ result | state' }}".

  Inductive t `{State.Trait} {Env : Set} (env_to_value : Env -> Value.t)
      (* Be aware of the order of parameters: the result and final state are at
         the beginning. This is due to the way polymorphic types for inductive
         work in Coq, and the fact that the result is always the same as we are
         in continuation passing style. *)
      (result : Value.t + Exception.t) (state' : State) :
      M -> State -> Prop :=
  | Pure :
    {{ env_to_value, state' | LowM.Pure result ⇓ result | state' }}
  | CallPrimitiveStateAllocImmediate
      (state : State) (v : Value.t)
      (k : Value.t -> M) :
    {{ env_to_value, state |
      k (Value.Pointer (Pointer.Immediate v)) ⇓ result
    | state' }} ->
    {{ env_to_value, state |
      LowM.CallPrimitive (Primitive.StateAlloc v) k ⇓ result
    | state' }}
  | CallPrimitiveStateAllocMutable
      (address : Address)
      (value : State.get_Set address)
      (value' : Value.t)
      (to_value : State.get_Set address -> Value.t)
      (state : State)
      (k : Value.t -> M) :
    let r := Value.Pointer (Pointer.mutable address to_value) in
    value' = to_value value ->
    State.read address state = None ->
    State.alloc_write address state value = Some state' ->
    {{ env_to_value, state | k r ⇓ result | state' }} ->
    {{ env_to_value, state |
      LowM.CallPrimitive (Primitive.StateAlloc value') k ⇓ result
    | state' }}
  | CallPrimitiveStateRead
      {A : Set} address path big_to_value projection injection to_value
      (value : State.get_Set address)
      (sub_value : A)
      (state : State)
      (k : Value.t -> M) :
    let mutable :=
      @Pointer.Mutable.Make
        Value.t Address (State.get_Set address) A
        address
        path
        big_to_value
        projection
        injection
        to_value in
    State.read address state = Some value ->
    projection value = Some sub_value ->
    {{ env_to_value, state |
      k (to_value sub_value) ⇓
      result
    | state' }} ->
    {{ env_to_value, state |
      LowM.CallPrimitive (Primitive.StateRead mutable) k ⇓
      result
    | state' }}
  | CallPrimitiveStateWrite
      {A : Set} address path big_to_value projection injection to_value
      (update : A) (update' : Value.t)
      (big_value new_big_value : State.get_Set address)
      (state state_inter : State)
      (k : Value.t -> M) :
    let mutable :=
      @Pointer.Mutable.Make
        Value.t Address (State.get_Set address) A
        address
        path
        big_to_value
        projection
        injection
        to_value in
    update' = to_value update ->
    State.read address state = Some big_value ->
    injection big_value update = Some new_big_value ->
    State.alloc_write address state new_big_value = Some state_inter ->
    {{ env_to_value, state_inter | k (Value.Tuple []) ⇓ result | state' }} ->
    {{ env_to_value, state |
      LowM.CallPrimitive (Primitive.StateWrite mutable update') k ⇓
      result
    | state' }}
  | CallPrimitiveEnvRead
      (state : State) (k : Value.t -> M) :
    {{ env_to_value, state | k (env_to_value env) ⇓ result | state' }} ->
    {{ env_to_value, state |
      LowM.CallPrimitive Primitive.EnvRead k ⇓ result
    | state' }}
  | CallPrimitiveGetAssociatedFunction
      (state : State)
      (ty : Ty.t) (name : string) (generic_tys : list Ty.t)
      (associated_function : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure :=
      Value.Closure (existS (Value.t, M) (associated_function generic_tys)) in
    M.IsAssociatedFunction ty name associated_function ->
    {{ env_to_value, state | k closure ⇓ result | state' }} ->
    {{ env_to_value, state |
      LowM.CallPrimitive
        (Primitive.GetAssociatedFunction ty name generic_tys) k ⇓
        result
    | state' }}
  | CallPrimitiveGetTraitMethod
      (state : State)
      (trait_name : string) (self_ty : Ty.t) (trait_tys : list Ty.t)
      (method_name : string) (generic_tys : list Ty.t)
      (method : list Ty.t -> list Value.t -> M)
      (k : Value.t -> M) :
    let closure :=
      Value.Closure (existS (Value.t, M) (method generic_tys)) in
    IsTraitMethod trait_name self_ty trait_tys method_name method ->
    {{ env_to_value, state | k closure ⇓ result | state' }} ->
    {{ env_to_value, state |
      LowM.CallPrimitive
        (Primitive.GetTraitMethod
          trait_name
          self_ty
          trait_tys
          method_name
          generic_tys)
        k ⇓
        result
    | state' }}
  | CallClosure
      (state state_inter : State)
      (f : list Value.t -> M) (args : list Value.t)
      (value : Value.t + Exception.t)
      (k : Value.t + Exception.t -> M) :
    let closure := Value.Closure (existS (Value.t, M) f) in
    {{ env_to_value, state | f args ⇓ value | state_inter }} ->
    {{ env_to_value, state_inter | k value ⇓ result | state' }} ->
    {{ env_to_value, state | LowM.CallClosure closure args k ⇓ result | state' }}

  where "{{ env , state | e ⇓ result | state' }}" :=
    (t env result state' e state).

  Definition pure (e : M) (result : Value.t + Exception.t) : Prop :=
    forall
      (State Address : Set) `(State.Trait State Address)
      (state : State) (env : Value.t),
    {{ env, state | e ⇓ result | state }}.
End Run.

(** Simplify the usual case of read of immediate value. *)
Lemma read_of_immediate (v : Value.t) :
  M.read (Value.Pointer (Pointer.Immediate v)) =
  M.pure v.
Proof.
  reflexivity.
Qed.

Ltac run_symbolic_state_read :=
  match goal with
  | |- Run.t _ _ _ (LowM.CallPrimitive (Primitive.StateRead ?address) _) _ =>
    let H := fresh "H" in
    epose proof (H := Run.CallPrimitiveStateRead _ _ _ address);
    eapply H; [reflexivity|];
    clear H
  end.

Ltac run_symbolic_state_write :=
  match goal with
  | |- Run.t ?env ?result ?state'
      (LowM.CallPrimitive (Primitive.StateWrite ?address ?value) ?k)
      ?state =>
    let H := fresh "H" in
    epose proof (H :=
      Run.CallPrimitiveStateWrite
        env result state' address value state _ k);
    apply H; [reflexivity|];
    clear H
  end.

Ltac run_symbolic_one_step :=
  match goal with
  | |- Run.t _ _ _ _ _ =>
    (* We do not use [Run.CallClosure] and let the user use existing lemma
       for this kind of case. *)
    apply Run.Pure ||
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
