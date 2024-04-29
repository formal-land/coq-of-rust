(** * The definition of a Rust monad with high-level types, for the simulations. *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.

Module Pointer.
  Inductive t (A : Set) : Set :=
  | Immediate (value : A)
  | Mutable {Address : Set} (address : Address) (path : Pointer.Path.t).
  Arguments Immediate {_}.
  Arguments Mutable {_ _}.

  Definition to_value_pointer {A : Set} (to_value : A -> Value.t) (pointer : t A) :
      CoqOfRust.M.Pointer.t Value.t :=
    match pointer with
    | Immediate v => CoqOfRust.M.Pointer.Immediate (to_value v)
    | Mutable address path => CoqOfRust.M.Pointer.Mutable address path
    end.
End Pointer.

Module Primitive.
  Inductive t : Set -> Set :=
  | StateAlloc {A : Set} (to_value : A -> Value.t) (value : A) : t (Pointer.t A)
  | StateRead {A : Set} (pointer : Pointer.t A) : t A
  | StateWrite {A : Set} (pointer : Pointer.t A) (update : A) : t unit
  | EnvRead {A : Set} : t A.
End Primitive.

Module Exception.
  Inductive t (R : Set) : Set :=
  (** exceptions for Rust's `return` *)
  | Return (value : R)
  (** exceptions for Rust's `continue` *)
  | Continue
  (** exceptions for Rust's `break` *)
  | Break
  (** escape from a match branch once we know that it is not valid *)
  | BreakMatch
  | Panic (message : string).
  Arguments Return {_}.
  Arguments Continue {_}.
  Arguments Break {_}.
  Arguments BreakMatch {_}.
  Arguments Panic {_}.
End Exception.

Module ClosureParams.
  Inductive t : Set :=
  | Empty
  | Cons {A : Set} `{ToValue A} (param : A) (params : t).

  Notation "<[ ]>" := Empty.
  Notation "<[ x ; .. ; y ]>" := (Cons x .. (Cons y Empty) ..).

  Fixpoint to_value (params : t) : list Value.t :=
    match params with
    | <[]> => []
    | Cons param params => φ param :: to_value params
    end.

  Module HasSetValue.
    Inductive t : ClosureParams.t -> forall {A : Set}, A -> Prop :=
    | Empty : t ClosureParams.Empty tt
    | Cons {A As : Set} `{ToValue A} (value : A) (params : ClosureParams.t) (values : As) :
        t params values ->
        t (ClosureParams.Cons value params) (value, values).
  End HasSetValue.
End ClosureParams.

Module LowM.
  Inductive t (A : Set) : Set :=
  | Pure (value : A)
  | CallPrimitive {B : Set} (primitive : Primitive.t B) (k : B -> t A)
  | CallClosure {B : Set}
      (to_value : B -> Value.t)
      (params : ClosureParams.t)
      (body : t (B + Exception.t Empty_set))
      (k : (B + Exception.t Empty_set) -> t A)
  | Impossible.
  Arguments Pure {_}.
  Arguments CallPrimitive {_ _}.
  Arguments CallClosure {_ _}.
  Arguments Impossible {_}.

  Fixpoint let_ {A B : Set} (e1 : t A) (e2 : A -> t B) : t B :=
    match e1 with
    | Pure v => e2 v
    | CallPrimitive primitive k =>
      CallPrimitive primitive (fun v => let_ (k v) e2)
    | CallClosure to_value params body k =>
      CallClosure to_value params body (fun v => let_ (k v) e2)
    | Impossible => Impossible
    end.
End LowM.

(** In the body of a function we can have a type for the parameter of the `return` keyword. *)
Definition MBody (A R : Set) : Set :=
  LowM.t (A + Exception.t R).

(** For the whole type of a function, the potential `return` that appear in the body are already
    handled. *)
Definition M (A : Set) : Set :=
  MBody A Empty_set.

Definition pure {A R : Set} (v : A) : MBody A R :=
  LowM.Pure (inl v).

Definition let_ {A B R : Set} (e1 : MBody A R) (e2 : A -> MBody B R) : MBody B R :=
  LowM.let_ e1 (fun v1 =>
  match v1 with
  | inl v1 => e2 v1
  | inr error => LowM.Pure (inr error)
  end).

Definition result_to_value {A R : Set} `{ToValue A} `{ToValue R} (result : A + Exception.t R) :
    Value.t + CoqOfRust.M.Exception.t :=
  match result with
  | inl v => inl (φ v)
  | inr exception =>
    inr match exception with
    | Exception.Return r => CoqOfRust.M.Exception.Return (φ r)
    | Exception.Continue => CoqOfRust.M.Exception.Continue
    | Exception.Break => CoqOfRust.M.Exception.Break
    | Exception.BreakMatch => CoqOfRust.M.Exception.BreakMatch
    | Exception.Panic message => CoqOfRust.M.Exception.Panic message
    end
  end.

(** This parameter is used as a marker to allow a monadic notation
    without naming all intermediate results. Computation represented using
    this markers can be translated to a regular monadic computation using
    [M.monadic] tactic. *)
Parameter run : forall {A R : Set}, MBody A R -> A.

Module Notations.
  Notation "'let-' a := b 'in' c" :=
    (LowM.let_ b (fun a => c))
      (at level 200, b at level 100, a name).

  Notation "'let*' a := b 'in' c" :=
    (let_ b (fun a => c))
      (at level 200, b at level 100, a name).

  Notation "'let*' ' a ':=' b 'in' c" :=
    (let_ b (fun a => c))
    (at level 200, a pattern, b at level 100, c at level 200).

  Notation "e (| e1 , .. , en |)" :=
    (run ((.. (e e1) ..) en))
    (at level 100).

  Notation "e (||)" :=
    (run e)
    (at level 100).
End Notations.
Import Notations.

(** A tactic that replaces all [M.run] markers with a bind operation.
    This allows to represent Rust programs without introducing
    explicit names for all intermediate computation results. *)
Ltac monadic e :=
  lazymatch e with
  | context ctxt [let v : _ := ?x in @?f v] =>
    refine (let_ _ _);
      [ monadic x
      | let v' := fresh v in
        intro v';
        let y := (eval cbn beta in (f v')) in
        lazymatch context ctxt [let v := x in y] with
        | let _ := x in y => monadic y
        | _ =>
          refine (let_ _ _);
            [ monadic y
            | let w := fresh "v" in
              intro w;
              let z := context ctxt [w] in
              monadic z
            ]
        end
      ]
  | context ctxt [run ?x] =>
    lazymatch context ctxt [run x] with
    | run x => monadic x
    | _ =>
      refine (let_ _ _);
        [ monadic x
        | let v := fresh "v" in
          intro v;
          let y := context ctxt [v] in
          monadic y
        ]
    end
  | _ =>
    lazymatch type of e with
    | MBody _ _ => exact e
    | _ => exact (pure e)
    end
  end.

Definition raise {A R : Set} (exception : Exception.t R) : MBody A R :=
  LowM.Pure (inr exception).

Definition return_ {R : Set} (value : R) : MBody R R :=
  raise (Exception.Return value).

Definition continue {R : Set} : MBody unit R :=
  raise Exception.Continue.

Definition break {R : Set} : MBody unit R :=
  raise Exception.Break.

Definition break_match {R : Set} : MBody unit R :=
  raise Exception.BreakMatch.

Definition panic {A R : Set} (message : string) : MBody A R :=
  raise (Exception.Panic message).

Definition call_primitive {A R : Set} (primitive : Primitive.t A) : MBody A R :=
  LowM.CallPrimitive primitive (fun result =>
  LowM.Pure (inl result)).

Definition alloc {A R : Set} `{ToValue A} (value : A) : MBody (Pointer.t A) R :=
  call_primitive (Primitive.StateAlloc φ value).

Definition read {A R : Set} (pointer : Pointer.t A) : MBody A R :=
  call_primitive (Primitive.StateRead pointer).

Definition write {A R : Set} (pointer : Pointer.t A) (update : A) : MBody unit R :=
  call_primitive (Primitive.StateWrite pointer update).

Definition copy {A R : Set} `{ToValue A} (p : Pointer.t A) : MBody (Pointer.t A) R :=
  let* v := read p in
  alloc v.

Definition catch {A R R' : Set} (body : MBody A R) (handler : Exception.t R -> MBody A R') :
    MBody A R' :=
  let- result := body in
  match result with
  | inl v => LowM.Pure (inl v)
  | inr exception => handler exception
  end.

Definition catch_return {R : Set} (body : MBody R R) : M R :=
  catch (R' := Empty_set)
    body
    (fun exception =>
      match exception with
      | Exception.Return r => pure r
      | Exception.Continue => raise Exception.Continue
      | Exception.Break => raise Exception.Break
      | Exception.BreakMatch => raise Exception.BreakMatch
      | Exception.Panic message => raise (Exception.Panic message)
      end
    ).

Definition catch_continue {R : Set} (body : MBody (Pointer.t unit) R) : MBody (Pointer.t unit) R :=
  catch
    body
    (fun exception =>
      match exception with
      | Exception.Continue => alloc tt
      | _ => raise exception
      end
    ).

Definition catch_break {R : Set} (body : MBody (Pointer.t unit) R) : MBody (Pointer.t unit) R :=
  catch
    body
    (fun exception =>
      match exception with
      | Exception.Break => alloc tt
      | _ => raise exception
      end
    ).

Definition call_closure {A R : Set} {H : ToValue A} (body : M A) : MBody A R :=
  catch (LowM.CallClosure φ body LowM.Pure) (fun exception =>
    match exception with
    | Exception.Return r => match r with end
    | Exception.Continue => raise Exception.Continue
    | Exception.Break => raise Exception.Break
    | Exception.BreakMatch => raise Exception.BreakMatch
    | Exception.Panic message => raise (Exception.Panic message)
    end
  ).

Definition read_env {A R : Set} : MBody A R :=
  call_primitive Primitive.EnvRead.

Definition impossible {A R : Set} : MBody A R :=
  LowM.Impossible.

(* Module EnvStateToValue.
  Record t (Env Address : Set) (get_Set : Address -> Set) : Set := {
    env_to_value : Env -> Value.t;
    cell_to_value : forall (address : Address), get_Set address -> Value.t;
  }.
End EnvStateToValue. *)

Module Run.
  Reserved Notation "{{ Address , env_to_value | e ~ result }}".

  Inductive t (Address : Set) {Env : Set} (env_to_value : Env -> Value.t)
      {A R : Set} `{ToValue A} `{ToValue R} :
      CoqOfRust.M.M -> MBody A R -> Prop :=
  | Pure (result : A + Exception.t R) :
    {{ Address, env_to_value |
      CoqOfRust.M.LowM.Pure (result_to_value result) ~
      LowM.Pure result
    }}
  | CallPrimitiveStateAlloc {B : Set} `{ToValue B}
      (value : B)
      (k' : Value.t -> CoqOfRust.M.M)
      (k : Pointer.t B -> MBody A R) :
    (forall (pointer : Pointer.t B),
      {{ Address, env_to_value |
        k' (Value.Pointer φ (Pointer.to_value_pointer φ pointer)) ~
        k pointer
      }}
    ) ->
    {{ Address, env_to_value |
      CoqOfRust.M.LowM.CallPrimitive (CoqOfRust.M.Primitive.StateAlloc (φ value)) k' ~
      LowM.CallPrimitive (Primitive.StateAlloc φ value) k
    }}
  | CallPrimitiveStateRead {B : Set}
      (to_value : B -> Value.t)
      (pointer : Pointer.t B)
      (k' : Value.t -> CoqOfRust.M.M)
      (k : B -> MBody A R) :
    (forall (value : B),
      {{ Address, env_to_value |
        k' (to_value value) ~
        k value
      }}
    ) ->
    {{ Address, env_to_value |
      CoqOfRust.M.LowM.CallPrimitive
        (CoqOfRust.M.Primitive.StateRead to_value (Pointer.to_value_pointer to_value pointer))
        k' ~
      LowM.CallPrimitive (Primitive.StateRead pointer) k
    }}
  | CallPrimitiveStateWrite {B : Set}
      (to_value : B -> Value.t)
      (pointer : Pointer.t B)
      (update : B)
      (k' : Value.t -> CoqOfRust.M.M)
      (k : unit -> MBody A R) :
    {{ Address, env_to_value |
      k' (Value.Tuple []) ~
      k tt
    }} ->
    {{ Address, env_to_value |
      CoqOfRust.M.LowM.CallPrimitive
        (CoqOfRust.M.Primitive.StateWrite
          to_value
          (Pointer.to_value_pointer to_value pointer)
          (to_value update)
        )
        k' ~
      LowM.CallPrimitive (Primitive.StateWrite pointer update) k
    }}
  | CallPrimitiveEnvRead
      (k' : Value.t -> CoqOfRust.M.M)
      (k : Env -> MBody A R) :
    (forall (env : Env),
      {{ Address, env_to_value |
        k' (env_to_value env) ~
        k env
      }}
    ) ->
    {{ Address, env_to_value |
      CoqOfRust.M.LowM.CallPrimitive CoqOfRust.M.Primitive.EnvRead k' ~
      LowM.CallPrimitive Primitive.EnvRead k
    }}
  | CallClosure {B : Set}
      (to_value : B -> Value.t)
      (body : M B)
      (k : B + Exception.t Empty_set -> MBody A R) :
    {{ Address, env_to_value |
      LowM.CallClosure e k ~
      LowM.CallClosure to_value body k
    }}

  where "{{ Address , env_to_value | untyped ~ typed }}" :=
    (t Address env_to_value untyped typed).
End Run.


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
    (* We do not use [Run.CallClosure] and intentionally let the user use existing lemma for this
       case. *)
    apply Run.Pure ||
    apply Run.CallPrimitiveStateAllocNone ||
    apply Run.CallPrimitiveEnvRead ||
    run_symbolic_state_read ||
    run_symbolic_state_write
  end.

Ltac run_symbolic :=
  repeat (
    cbn ||
    run_symbolic_one_step
  ).
