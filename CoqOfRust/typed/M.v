(** * The definition of a Rust monad with high-level types, for the simulations. *)
Require Import CoqOfRust.CoqOfRust.

Module Pointer.
  Inductive t (A : Set) : Set :=
  | Immediate (value : A)
  | Mutable {Address Big_A : Set}
      (address : Address)
      (projection : Big_A -> option A)
      (injection : A -> Big_A -> option Big_A).
  Arguments Immediate {_}.
  Arguments Mutable {_ _ _}.
End Pointer.

Module Primitive.
  Inductive t : Set -> Set :=
  | StateAlloc {A : Set} (value : A) : t (Pointer.t A)
  | StateRead {Address A : Set} (address : Address) : t A
  | StateWrite {Address A : Set} (address : Address) (value : A) : t unit
  | EnvRead {A : Set} : t A.
End Primitive.

Module LowM.
  Inductive t (A : Set) : Set :=
  | Pure (value : A)
  | CallPrimitive {B : Set} (primitive : Primitive.t B) (k : B -> t A)
  | CallClosure {B : Set} (body : t B) (k : B -> t A)
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
    | CallClosure body k =>
      CallClosure body (fun v => let_ (k v) e2)
    | Impossible => Impossible
    end.
End LowM.

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

Definition alloc {A R : Set} (value : A) : MBody (Pointer.t A) R :=
  call_primitive (Primitive.StateAlloc value).

Definition read {A R : Set} (p : Pointer.t A) : MBody A R :=
  match p with
  | Pointer.Immediate v => LowM.Pure (inl v)
  | Pointer.Mutable address projection injection =>
    let* v := call_primitive (Primitive.StateRead address) in
    match projection v with
    | Some v => LowM.Pure (inl v)
    | None => LowM.Impossible
    end
  end.

Definition write {A R : Set} (p : Pointer.t A) (update : A) : MBody unit R :=
  match p with
  | Pointer.Immediate _ => LowM.Impossible
  | Pointer.Mutable address projection injection =>
    let* value := call_primitive (Primitive.StateRead address) in
    match injection update value with
    | Some value => call_primitive (Primitive.StateWrite address value)
    | None => LowM.Impossible
    end
  end.

Definition copy {A R : Set} (p : Pointer.t A) : MBody (Pointer.t A) R :=
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

Definition call_closure {A R : Set} (body : M A) : MBody A R :=
  catch (LowM.CallClosure body LowM.Pure) (fun exception =>
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

(* Definition loop (body : M) : M :=
  LowM.Loop
    (catch_continue body)
    (fun result =>
      catch_break (LowM.Pure result)). *)

Module State.
  Class Trait (State Address : Set) : Type := {
    get_Set : Address -> Set;
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
