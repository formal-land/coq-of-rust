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
    (method : list Ty.t -> list A.t -> M) :
    Prop :=
  exists (instance : Instance.t),
  M.IsTraitInstance
    trait_name
    self_ty
    trait_tys
    instance /\
  List.assoc instance method_name = Some (InstanceField.Method method).

Module Run.
  Reserved Notation "{{ env  , state | e ⇓ result | state' }}".

  Inductive t `{State.Trait} {Env : Set} `{ToValue Env} (env : Env)
      (* Be aware of the order of parameters: the result and final state are at
         the beginning. This is due to the way polymorphic types for inductive
         work in Coq, and the fact that the result is always the same as we are
         in continuation passing style. *)
      (result : A.t + Exception.t) (state' : State) :
      M -> State -> Prop :=
  | Pure :
    {{ env, state' | LowM.Pure result ⇓ result | state' }}
  | CallPrimitiveStateAllocImmediate
      (state : State) (value : A.t)
      {B : Set} (next_to_value : B -> Value.t) (next : B)
      (k : A.t -> M) :
    Value.Pointer (Pointer.Immediate (A.to_value value)) = next_to_value next ->
    {{ env, state |
      k (A.Make (to_value := next_to_value) next) ⇓ result
    | state' }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateAlloc value) k ⇓ result
    | state' }}
  | CallPrimitiveStateAllocMutable
      (address : Address)
      (value : State.get_Set address) `{ToValue (State.get_Set address)}
      (to_value : State.get_Set address -> Value.t)
      (state : State)
      {B : Set} `{ToValue B} (next : B)
      (k : A.t -> M) :
    Value.Pointer (Pointer.mutable address to_value) = φ next ->
    State.read address state = None ->
    State.alloc_write address state value = Some state' ->
    {{ env, state |
      k (A.make next) ⇓ result
    | state' }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateAlloc (A.make value)) k ⇓ result
    | state' }}
  | CallPrimitiveStateRead
      {A : Set} {to_value : A -> Value.t} address path big_to_value projection injection
      (value : State.get_Set address)
      (sub_value : A)
      (state : State)
      (k : A.t -> M) :
    let mutable :=
      Pointer.Mutable.Make
        (Value := Value.t) (A := A) (to_value := to_value) (Address := Address)
        (Big_A := State.get_Set address)
        address
        path
        big_to_value
        projection
        injection in
    State.read address state = Some value ->
    projection value = Some sub_value ->
    {{ env, state |
      k (A.Make (to_value := to_value) sub_value) ⇓
      result
    | state' }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateRead mutable) k ⇓
      result
    | state' }}
  | CallPrimitiveStateWrite
      {A : Set} {to_value : A -> Value.t} address path big_to_value projection injection
      (value : A)
      (big_value new_big_value : State.get_Set address)
      (state state_inter : State)
      (k : A.t -> M) :
    let mutable :=
      Pointer.Mutable.Make
        (Value := Value.t) (A := A) (to_value := to_value) (Address := Address)
        (Big_A := State.get_Set address)
        address
        path
        big_to_value
        projection
        injection in
    State.read address state = Some big_value ->
    injection big_value value = Some new_big_value ->
    State.alloc_write address state new_big_value = Some state_inter ->
    {{ env, state_inter |
      k (A.make tt) ⇓
      result
    | state' }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.StateWrite mutable (A.Make (to_value := to_value) value)) k ⇓
      result
    | state' }}
  | CallPrimitiveGetSubPointer {A Sub_A : Set} {to_value : A -> Value.t}
      (mutable : Pointer.Mutable.t Value.t to_value)
      index sub_projection sub_injection sub_to_value
      (state : State)
      {B : Set} `{ToValue B} (next : B)
      (k : A.t -> M) :
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
    Value.Pointer (Pointer.Mutable (Pointer.Mutable.get_sub
      mutable index sub_projection sub_injection sub_to_value
    )) = φ next ->
    {{ env, state |
      k (A.make next) ⇓
      result
    | state' }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.GetSubPointer mutable index) k ⇓
      result
    | state' }}
  | CallPrimitiveEnvRead
      (state : State) (k : A.t -> M) :
    {{ env, state |
      k (A.make env) ⇓
      result
    | state' }} ->
    {{ env, state |
      LowM.CallPrimitive Primitive.EnvRead k ⇓
      result
    | state' }}
  | CallPrimitiveGetAssociatedFunction
      (state : State)
      (ty : Ty.t) (name : string) (generic_tys : list Ty.t)
      (associated_function : list Ty.t -> list A.t -> M)
      {B : Set} `{ToValue B} (next : B)
      (k : A.t -> M) :
    let closure :=
      Value.Closure (existS (A.t, M) (associated_function generic_tys)) in
    M.IsAssociatedFunction ty name associated_function ->
    closure = φ next ->
    {{ env, state |
      k (A.make next) ⇓
      result
    | state' }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.GetAssociatedFunction ty name generic_tys) k ⇓
      result
    | state' }}
  | CallPrimitiveGetTraitMethod
      (state : State)
      (trait_name : string) (self_ty : Ty.t) (trait_tys : list Ty.t)
      (method_name : string) (generic_tys : list Ty.t)
      (method : list Ty.t -> list A.t -> M)
      {B : Set} `{ToValue B} (next : B)
      (k : A.t -> M) :
    let closure :=
      Value.Closure (existS (A.t, M) (method generic_tys)) in
    IsTraitMethod trait_name self_ty trait_tys method_name method ->
    closure = φ next ->
    {{ env, state |
      k (A.make next) ⇓
      result
    | state' }} ->
    {{ env, state |
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
      (f : list A.t -> M) (args : list A.t)
      (value : A.t + Exception.t)
      {B : Set} `{ToValue B} (closure' : B)
      (k : A.t + Exception.t -> M) :
    let closure := Value.Closure (existS (A.t, M) f) in
    closure = φ closure' ->
    {{ env, state | f args ⇓ value | state_inter }} ->
    {{ env, state_inter | k value ⇓ result | state' }} ->
    {{ env, state |
      LowM.CallClosure (A.Make (to_value := φ) closure') args k ⇓
      result
    | state' }}

  where "{{ env , state | e ⇓ result | state' }}" :=
    (t env result state' e state).

  Definition pure (e : M) (result : A.t + Exception.t) : Prop :=
    forall
      (State Address : Set) `(State.Trait State Address)
      (Env : Set) `(ToValue Env) (env : Env)
      (state : State),
    {{ env, state | e ⇓ result | state }}.
End Run.

Module SubPointer.
  Module Runner.
    Module Valid.
      Inductive t {A Sub_A : Set} `{ToValue A} `{ToValue Sub_A} :
          SubPointer.Runner.t A Sub_A -> Prop :=
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

  Lemma run
      {A Sub_A : Set} `{ToValue A} `{ToValue Sub_A}
      {runner : SubPointer.Runner.t A Sub_A}
      (H_runner : Runner.Valid.t runner)
      (mutable : Pointer.Mutable.t (A := A) Value.t φ)
      `{State.Trait} {Env : Set} `{ToValue Env} (env : Env)
      (result : A.t + Exception.t) (state state' : State) (k : A.t -> M)
      {B : Set} `{ToValue B} (next : B)
      (index : Pointer.Index.t) :
    index = runner.(SubPointer.Runner.index) ->
    Value.Pointer (Pointer.Mutable (SubPointer.get_sub mutable runner)) = φ next ->
    {{ env, state |
      k (A.make next) ⇓
      result
    | state' }} ->
    {{ env, state |
      LowM.CallPrimitive (Primitive.GetSubPointer mutable index) k ⇓
      result
    | state' }}.
  Proof.
    intros.
    destruct H_runner.
    eapply Run.CallPrimitiveGetSubPointer; sfirstorder.
  Qed.
End SubPointer.

Ltac run_symbolic_state_read :=
  match goal with
  | |- Run.t _ _ _ _ (LowM.CallPrimitive (Primitive.StateRead (
      Pointer.Mutable.Make ?address _ _ _ _
    )) _) _ =>
    let H := fresh "H" in
    epose proof (H := Run.CallPrimitiveStateRead _ _ _ _ address);
    eapply H; [reflexivity | reflexivity |];
    clear H
  end.

Ltac run_symbolic_state_write :=
  match goal with
  | |- Run.t ?env ?env_to_value ?result ?state'
      (LowM.CallPrimitive (Primitive.StateWrite (
        Pointer.Mutable.Make ?address ?path ?big_to_value ?projection ?injection
      ) ?value') ?k)
      ?state =>
    let H := fresh "H" in
    epose proof (H :=
      Run.CallPrimitiveStateWrite
        env env_to_value result state' address path big_to_value projection injection _
        value' _ _ _ _ k
    );
    apply H; try reflexivity;
    clear H
  end.

Ltac run_symbolic_one_step :=
  match goal with
  | |- Run.t _ _ _ _ _ _ =>
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
