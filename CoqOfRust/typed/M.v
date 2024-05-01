(** * The definition of a Rust monad with high-level types, for the simulations. *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.simulations.M.

Import List.ListNotations.

Local Open Scope list.

(** ** Translation from a high-level type to a value. *)

Class ToValue (A : Set) : Set := {
  Φ : Ty.t;
  φ : A -> Value.t;
}.
Arguments Φ _ {_}.

Module Empty_setIsToValue.
  Global Instance I : ToValue Empty_set := {
    Φ := Ty.path "never";
    φ v := match v with end;
  }.
End Empty_setIsToValue.

Module StringIsToValue.
  Global Instance I : ToValue string := {
    Φ := Ty.path "str";
    φ v := Value.String v;
  }.
End StringIsToValue.

(** For tuples we provide a canonical way to convert to values. *)
Module TupleIsToValue.
  Global Instance I0 : ToValue unit := {
    Φ := Ty.tuple [];
    φ 'tt := Value.Tuple [];
  }.

  Global Instance I2 (A1 A2 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2) :
      ToValue (A1 * A2) := {
    Φ := Ty.tuple [Φ A1; Φ A2];
    φ '(x1, x2) := Value.Tuple [φ x1; φ x2];
  }.

  Global Instance I3 (A1 A2 A3 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3) :
      ToValue (A1 * A2 * A3) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3];
    φ '(x1, x2, x3) :=
      Value.Tuple [φ x1; φ x2; φ x3];
  }.

  Global Instance I4 (A1 A2 A3 A4 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3)
      (_ : ToValue A4) :
      ToValue (A1 * A2 * A3 * A4) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3; Φ A4];
    φ '(x1, x2, x3, x4) :=
      Value.Tuple [φ x1; φ x2; φ x3; φ x4];
  }.

  Global Instance I5 (A1 A2 A3 A4 A5 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3)
      (_ : ToValue A4)
      (_ : ToValue A5) :
      ToValue (A1 * A2 * A3 * A4 * A5) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3; Φ A4; Φ A5];
    φ '(x1, x2, x3, x4, x5) :=
      Value.Tuple [φ x1; φ x2; φ x3; φ x4; φ x5];
  }.

  Global Instance I6 (A1 A2 A3 A4 A5 A6 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3)
      (_ : ToValue A4)
      (_ : ToValue A5)
      (_ : ToValue A6) :
      ToValue (A1 * A2 * A3 * A4 * A5 * A6) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3; Φ A4; Φ A5; Φ A6];
    φ '(x1, x2, x3, x4, x5, x6) :=
      Value.Tuple [φ x1; φ x2; φ x3; φ x4; φ x5; φ x6];
  }.

  Global Instance I7 (A1 A2 A3 A4 A5 A6 A7 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3)
      (_ : ToValue A4)
      (_ : ToValue A5)
      (_ : ToValue A6)
      (_ : ToValue A7) :
      ToValue (A1 * A2 * A3 * A4 * A5 * A6 * A7) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3; Φ A4; Φ A5; Φ A6; Φ A7];
    φ '(x1, x2, x3, x4, x5, x6, x7) :=
      Value.Tuple [φ x1; φ x2; φ x3; φ x4; φ x5; φ x6; φ x7];
  }.

  Global Instance I8 (A1 A2 A3 A4 A5 A6 A7 A8 : Set)
      (_ : ToValue A1)
      (_ : ToValue A2)
      (_ : ToValue A3)
      (_ : ToValue A4)
      (_ : ToValue A5)
      (_ : ToValue A6)
      (_ : ToValue A7)
      (_ : ToValue A8) :
      ToValue (A1 * A2 * A3 * A4 * A5 * A6 * A7 * A8) := {
    Φ := Ty.tuple [Φ A1; Φ A2; Φ A3; Φ A4; Φ A5; Φ A6; Φ A7; Φ A8];
    φ '(x1, x2, x3, x4, x5, x6, x7, x8) :=
      Value.Tuple [φ x1; φ x2; φ x3; φ x4; φ x5; φ x6; φ x7; φ x8];
  }.
End TupleIsToValue.

Module Pointer.
  Module Address.
    Inductive t (A : Set) : Set :=
    | Null
    | Immediate (value : A)
    | Mutable {Address : Set} (address : Address).
    Arguments Null {_}.
    Arguments Immediate {_}.
    Arguments Mutable {_ _}.

    Definition to_address {A : Set} (to_value : A -> Value.t) (address : t A) :
        CoqOfRust.M.Pointer.Address.t Value.t :=
      match address with
      | Null => CoqOfRust.M.Pointer.Address.Null
      | Immediate v => CoqOfRust.M.Pointer.Address.Immediate (to_value v)
      | Mutable address => CoqOfRust.M.Pointer.Address.Mutable address
      end.

    Definition map {A A' : Set} (projection : A -> option A') (address : t A) : t A' :=
      match address with
      | Null => Null
      | Immediate v =>
        match projection v with
        | Some v' => Immediate v'
        | None => Null (* This is where the null addresses can be created *)
        end
      | Mutable address => Mutable address
      end.
  End Address.

  (** Information about the origin of the pointer in case of sub-pointer. *)
  Module Origin.
    Inductive t (A : Set) : Set :=
    | Make {Big_A : Set}
        (big_to_value : Big_A -> Value.t)
        (projection : Big_A -> option A)
        (injection : Big_A -> A -> option Big_A).
    Arguments Make {_ _}.
  End Origin.

  Inductive t (A : Set) `{ToValue A} : Set :=
  | Make
      (origin : Origin.t A)
      (address : Address.t A)
      (path : Pointer.Path.t).
  Arguments Make {_ _}.

  Definition to_pointer {A : Set} `{ToValue A} (pointer : t A) : CoqOfRust.M.Pointer.t Value.t :=
    let 'Make origin address path := pointer in
    let 'Origin.Make big_to_value projection injection := origin in
    CoqOfRust.M.Pointer.Make
      big_to_value
      φ
      projection
      injection
      (Address.to_address φ address)
      path.

  (* Definition map {Big Small : Set}
      (pointer : t Big)
      (index : Pointer.Index.t)
      (to_value : Small -> Value.t)
      (projection : Big -> option Small)
      (injection : Big -> Small -> option Big) :
      t Small :=
    let 'Make big_to_value to_value projection' injection' address path := pointer in
    Make
      big_to_value
      to_value
      address
      (path ++ [index])
      (fun big_big =>
        match projection' big_big with
        | Some big => projection big
        | None => None
        end
      )
      (fun big_big small =>
        match projection' big_big with
        | Some big =>
          match injection big small with
          | Some big' => injection' big_big big'
          | None => None
          end
        | None => None
        end
      ). *)

  (* Definition to_value_pointer {A : Set} (pointer : t A) : CoqOfRust.M.Pointer.t Value.t :=
    let 'Make address projection injection := pointer in
    let address :=
      match address with
      | Address.Immediate v => CoqOfRust.M.Pointer.Address.Immediate (to_value v)
      | Address.Mutable address => CoqOfRust.M.Pointer.Address.Mutable address
      end in
    {|
      CoqOfRust.M.Pointer.address := address;
      CoqOfRust.M.Pointer.path := path;
    |}. *)
End Pointer.

Module Primitive.
  Inductive t : Set -> Set :=
  | StateAlloc {A : Set} `{ToValue A} (value : A) : t (Pointer.t A)
  | StateRead {A : Set} `{ToValue A} (pointer : Pointer.t A) : t A
  | StateWrite {A : Set} `{ToValue A} (pointer : Pointer.t A) (update : A) : t unit
  | MakeSubPointer {A A' : Set} `{ToValue A} `{ToValue A'}
      (pointer : Pointer.t A)
      (index : Pointer.Index.t)
      (projection : A -> option A')
      (injection : A -> A' -> option A) :
    t (Pointer.t A')
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

  Fixpoint to_value (params : t) : list Value.t :=
    match params with
    | Empty => []
    | Cons param params => φ param :: to_value params
    end.

  Module HasSetValue.
    Inductive t : ClosureParams.t -> forall {A : Set}, A -> Prop :=
    | Empty : t ClosureParams.Empty tt
    | Single {A : Set} `{ToValue A} (value : A) :
        t (ClosureParams.Cons value ClosureParams.Empty) value
    | Cons {A As : Set} `{ToValue A} (value : A) (params : ClosureParams.t) (values : As) :
        t params values ->
        t (ClosureParams.Cons value params) (value, values).
  End HasSetValue.
End ClosureParams.

Module LowM.
  Inductive t (A : Set) : Set :=
  | Pure (value : A)
  | CallPrimitive {B : Set} (primitive : Primitive.t B) (k : B -> t A)
  | CallClosure {B Params : Set} `{ToValue B}
      (closure : Params -> t (B + Exception.t Empty_set))
      (params : ClosureParams.t)
      (k : (B + Exception.t Empty_set) -> t A)
  | Impossible.
  Arguments Pure {_}.
  Arguments CallPrimitive {_ _}.
  Arguments CallClosure {_ _ _ _}.
  Arguments Impossible {_}.

  Fixpoint let_ {A B : Set} (e1 : t A) (e2 : A -> t B) : t B :=
    match e1 with
    | Pure v => e2 v
    | CallPrimitive primitive k =>
      CallPrimitive primitive (fun v => let_ (k v) e2)
    | CallClosure params body k =>
      CallClosure params body (fun v => let_ (k v) e2)
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

Definition result_to_value {A R : Set} `{ToValue R}
    (to_value : A -> Value.t) (result : A + Exception.t R) :
    Value.t + CoqOfRust.M.Exception.t :=
  match result with
  | inl v => inl (to_value v)
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

  Notation "<[ ]>" := ClosureParams.Empty.
  Notation "<[ x ; .. ; y ]>" :=
    (ClosureParams.Cons x .. (ClosureParams.Cons y ClosureParams.Empty) ..).
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

Definition impossible {A R : Set} : MBody A R :=
  LowM.Impossible.

Definition call_primitive {A R : Set} (primitive : Primitive.t A) : MBody A R :=
  LowM.CallPrimitive primitive (fun result =>
  LowM.Pure (inl result)).

Definition alloc {A R : Set} `{ToValue A} (value : A) : MBody (Pointer.t A) R :=
  call_primitive (Primitive.StateAlloc value).

Definition read {A R : Set} `{ToValue A} (pointer : Pointer.t A) : MBody A R :=
  call_primitive (Primitive.StateRead pointer).

Definition write {A R : Set} `{ToValue A} (pointer : Pointer.t A) (update : A) : MBody unit R :=
  call_primitive (Primitive.StateWrite pointer update).

Definition make_sub_pointer {A A' R : Set} `{ToValue A} `{ToValue A'}
    (pointer : Pointer.t A) (index : Pointer.Index.t)
    (projection : A -> option A') (injection : A -> A' -> option A) :
    MBody (Pointer.t A') R :=
  call_primitive (Primitive.MakeSubPointer pointer index projection injection).

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

Definition call_closure {Params A R : Set} `{ToValue A}
    (body : Params -> M A)
    (params : ClosureParams.t) :
    MBody A R :=
  catch (LowM.CallClosure body params LowM.Pure) (fun exception =>
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

Module Run.
  Reserved Notation "{{ Address , env_to_value | e ~ result }}".

  Inductive t (Address : Set) {Env : Set} (env_to_value : Env -> Value.t)
      {A R : Set} `{ToValue A} `{ToValue R} :
      CoqOfRust.M.M -> MBody A R -> Prop :=
  | Pure
      (result : A + Exception.t R)
      (result' : Value.t + CoqOfRust.M.Exception.t) :
    result' = result_to_value φ result ->
    {{ Address, env_to_value |
      CoqOfRust.M.LowM.Pure result' ~
      LowM.Pure result
    }}
  | CallPrimitiveStateAlloc {B : Set} `{ToValue B}
      (value : B)
      (k' : Value.t -> CoqOfRust.M.M)
      (k : Pointer.t B -> MBody A R) :
    (forall (address : Pointer.Address.t B),
      let pointer :=
        Pointer.Make
          (Pointer.Origin.Make φ (fun x => Some x) (fun _ x => Some x))
          address
          [] in
      {{ Address, env_to_value |
        k' (Value.Pointer (Pointer.to_pointer pointer)) ~
        k pointer
      }}
    ) ->
    {{ Address, env_to_value |
      CoqOfRust.M.LowM.CallPrimitive (CoqOfRust.M.Primitive.StateAlloc (φ value)) k' ~
      LowM.CallPrimitive (Primitive.StateAlloc value) k
    }}
  | CallPrimitiveStateRead {B : Set} `{ToValue B}
      origin address path
      pointer'
      (k' : Value.t -> CoqOfRust.M.M)
      (k : B -> MBody A R) :
    let pointer : Pointer.t B := Pointer.Make origin address path in
    pointer' = Pointer.to_pointer pointer ->
    (forall (value : B),
      {{ Address, env_to_value |
        k' (φ value) ~
        k value
      }}
    ) ->
    {{ Address, env_to_value |
      CoqOfRust.M.LowM.CallPrimitive
        (CoqOfRust.M.Primitive.StateRead pointer')
        k' ~
      LowM.CallPrimitive (Primitive.StateRead pointer) k
    }}
  | CallPrimitiveStateWrite {B : Set} `{ToValue B}
      origin address path
      (update : B)
      (k' : Value.t -> CoqOfRust.M.M)
      (k : unit -> MBody A R) :
    let pointer : Pointer.t B := Pointer.Make origin address path in
    {{ Address, env_to_value |
      k' (Value.Tuple []) ~
      k tt
    }} ->
    {{ Address, env_to_value |
      CoqOfRust.M.LowM.CallPrimitive
        (CoqOfRust.M.Primitive.StateWrite
          (Pointer.to_pointer pointer)
          (φ update)
        )
        k' ~
      LowM.CallPrimitive (Primitive.StateWrite pointer update) k
    }}
  | CallPrimitiveMakeSubPointer {Big_B B Sub_B : Set} `{ToValue B} `{ToValue Sub_B}
      (big_to_value : Big_B -> Value.t) projection injection
      address path
      index sub_projection sub_injection
      pointer'
      (k' : Value.t -> CoqOfRust.M.M)
      (k : Pointer.t Sub_B -> MBody A R) :
    let origin : Pointer.Origin.t B := Pointer.Origin.Make big_to_value projection injection in
    let pointer : Pointer.t B := Pointer.Make origin address path in
    let sub_origin : Pointer.Origin.t Sub_B :=
      Pointer.Origin.Make
        big_to_value
        (fun big_b =>
          match projection big_b with
          | Some b => sub_projection b
          | None => None
          end)
        (fun big_b new_sub_b =>
          match projection big_b with
          | Some b =>
            match sub_injection b new_sub_b with
            | Some new_b => injection big_b new_b
            | None => None
            end
          | None => None
          end) in
    let sub_pointer : Pointer.t Sub_B :=
      Pointer.Make
        sub_origin
        (Pointer.Address.map sub_projection address)
        (path ++ [index]) in
    pointer' = Pointer.to_pointer pointer ->
    (* Communtativity of the read *)
    (forall (b : B),
      Option.map (sub_projection b) φ =
      Value.read_path (φ b) [index]
    ) ->
    (* Communtativity of the write *)
    (forall (b : B) (sub_b : Sub_B),
      Option.map (sub_injection b sub_b) φ =
      Value.write_value (φ b) [index] (φ sub_b)
    ) ->
    {{ Address, env_to_value |
      k' (Value.Pointer (Pointer.to_pointer sub_pointer)) ~
      k sub_pointer
    }} ->
    {{ Address, env_to_value |
      CoqOfRust.M.LowM.CallPrimitive
        (CoqOfRust.M.Primitive.MakeSubPointer
          pointer'
          index
        )
        k' ~
      LowM.CallPrimitive (Primitive.MakeSubPointer pointer index sub_projection sub_injection) k
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
  | CallClosure {B Params : Set} `{ToValue B}
      (closure : Params -> M B)
      (params : ClosureParams.t)
      (params_set_value : Params)
      (closure' : Value.t)
      (closure_content' : list Value.t -> CoqOfRust.M.M)
      params'
      (k' : Value.t + CoqOfRust.M.Exception.t -> CoqOfRust.M.M)
      (k : B + Exception.t Empty_set -> MBody A R) :
    closure' = M.closure closure_content' ->
    params' = ClosureParams.to_value params ->
    ClosureParams.HasSetValue.t params params_set_value ->
    {{ Address, env_to_value |
      closure_content' params' ~
      closure params_set_value
    }} ->
    (forall (result : B + Exception.t Empty_set),
      {{ Address, env_to_value |
        k' (result_to_value φ result) ~
        k result
      }}
    ) ->
    {{ Address, env_to_value |
      CoqOfRust.M.LowM.CallClosure closure' params' k' ~
      LowM.CallClosure closure params k
    }}

  where "{{ Address , env_to_value | untyped ~ typed }}" :=
    (t Address env_to_value untyped typed).
End Run.

Import Run.

Ltac run_symbolic_state_read :=
  match goal with
  | |- {{ ?Address, ?env_to_value |
      CoqOfRust.M.LowM.CallPrimitive
        (CoqOfRust.M.Primitive.StateRead ?pointer')
        ?k' ~
      LowM.CallPrimitive (Primitive.StateRead (Pointer.Make ?origin ?address ?path)) ?k
    }} =>
      let H := fresh "H" in
      pose proof (H :=
        Run.CallPrimitiveStateRead Address env_to_value origin address path k' k
      );
      apply H;
      clear H
  end.

(* Ltac run_symbolic_state_read :=
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
  ). *)
