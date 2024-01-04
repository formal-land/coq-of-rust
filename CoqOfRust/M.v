(** * The definition of a Rust monad. *)
Require Coq.Strings.String.

Local Open Scope list.

Inductive sigS {A : Type} (P : A -> Set) : Set :=
| existS : forall (x : A), P x -> sigS P.
Arguments existS {_ _}.

Reserved Notation "{ x @ P }" (at level 0, x at level 99).
Reserved Notation "{ x : A @ P }" (at level 0, x at level 99).
Reserved Notation "{ ' pat : A @ P }"
  (at level 0, pat strict pattern, format "{ ' pat : A @ P }").

Notation "{ x @ P }" := (sigS (fun x => P)) : type_scope.
Notation "{ x : A @ P }" := (sigS (A := A) (fun x => P)) : type_scope.
Notation "{ ' pat : A @ P }" := (sigS (A := A) (fun pat => P)) : type_scope.

Module Ref.
  Inductive t (A : Set) : Set :=
  (** Can be produced from [Imm] referencing on sum types. *)
  | Null : t A
  | Imm : A -> t A
  | MutRef {Address B : Set} (address : Address)
      (projection : B -> option A) (injection : A -> B -> option B) :
      t A.
  Arguments Null {_}.
  Arguments Imm {_}.
  Arguments MutRef {_ _ _}.

  (** For the case where the reference covers the whole address. *)
  Definition mut_ref {Address A : Set} (address : Address) : t A :=
    MutRef address (fun v => Some v) (fun v _ => Some v).

  Definition map {Big Small : Set}
      (projection : Big -> option Small)
      (injection : Small -> Big -> option Big)
      (r : t Big)
      : t Small :=
    match r with
    | Null => Null
    | Imm big =>
      match projection big with
      | Some small => Imm small
      | None => Null
      end
    | MutRef address projection' injection' =>
      MutRef address
        (fun big_big =>
          match projection' big_big with
          | Some big => projection big
          | None => None
          end
        )
        (fun small big_big =>
          match projection' big_big with
          | Some big =>
            match injection small big with
            | Some big' => injection' big' big_big
            | None => None
            end
          | None => None
          end
        )
    end.
End Ref.
Definition Ref := Ref.t.

Module Primitive.
  Inductive t : Set -> Set :=
  | StateAlloc {A : Set} : A -> t (Ref.t A)
  | StateRead {Address A : Set} : Address -> t A
  | StateWrite {Address A : Set} : Address -> A -> t unit
  | EnvRead {A : Set} : t A
  .
End Primitive.
Definition Primitive : Set -> Set := Primitive.t.

Module LowM.
  Inductive t (A : Set) : Set :=
  | Pure : A -> t A
  | CallPrimitive {B : Set} : Primitive B -> (B -> t A) -> t A
  | Cast {B1 B2 : Set} : B1 -> (B2 -> t A) -> t A
  | Loop {B : Set} : t B -> (B -> bool) -> (B -> t A) -> t A
  | Impossible : t A
  | Call {B : Set} : t B -> (B -> t A) -> t A.
  Arguments Pure {_}.
  Arguments CallPrimitive {_ _}.
  Arguments Cast {_ _ _}.
  Arguments Loop {_ _}.
  Arguments Impossible {_}.
  Arguments Call {_ _}.

  Fixpoint let_ {A B : Set} (e1 : t A) (f : A -> t B) : t B :=
    match e1 with
    | Pure v => f v
    | CallPrimitive primitive k =>
      CallPrimitive primitive (fun v => let_ (k v) f)
    | Cast v k =>
      Cast v (fun v' => let_ (k v') f)
    | Loop body is_break k => Loop body is_break (fun v => let_ (k v) f)
    | Impossible => Impossible
    | Call e k => Call e (fun v => let_ (k v) f)
    end.
End LowM.
Definition LowM : Set -> Set := LowM.t.

Module Exception.
  Inductive t : Set :=
  (** exceptions for Rust's `return` *)
  | Return {A : Set} : A -> t
  (** exceptions for Rust's `continue` *)
  | Continue : t
  (** exceptions for Rust's `break` *)
  | Break : t
  (** to translate the [match] patterns with (de)references *)
  | BreakMatch : t
  | Panic : Coq.Strings.String.string -> t.
End Exception.
Definition Exception : Set := Exception.t.

Definition M (A : Set) : Set :=
  LowM (A + Exception).

Definition pure {A : Set} (v : A) : M A :=
  LowM.Pure (inl v).

Definition let_ {A B : Set} (e1 : M A) (e2 : A -> M B) : M B :=
  LowM.let_ e1 (fun v1 =>
  match v1 with
  | inl v1 => e2 v1
  | inr error => LowM.Pure (inr error)
  end).

Module Option.
  Definition bind {A B : Set} (x : option A) (f : A -> option B) : option B :=
    match x with
    | Some x => f x
    | None => None
    end.
End Option.

Module Notations.
  Notation "'let-' a := b 'in' c" :=
    (LowM.let_ b (fun a => c))
      (at level 200, b at level 100, a name).

  Notation "'let*' a := b 'in' c" :=
    (let_ b (fun a => c))
      (at level 200, b at level 100, a name).

  Notation "'let*' a : T := b 'in' c" :=
    (let_ b (fun (a : T) => c))
      (at level 200, T constr, b at level 100, a name).

  Notation "'let*' ' a ':=' b 'in' c" :=
    (let_ b (fun a => c))
    (at level 200, a pattern, b at level 100, c at level 200).
End Notations.
Import Notations.

Definition cast {A B : Set} (v : A) : M B :=
  LowM.Cast (inl (B := Exception) v) LowM.Pure.

Definition raise {A : Set} (exception : Exception) : M A :=
  LowM.Pure (inr exception).

Definition return_ {A R : Set} (r : R) : M A :=
  raise (Exception.Return r).

Definition continue {A : Set} : M A :=
  raise Exception.Continue.

Definition break {A : Set} : M A :=
  raise Exception.Break.

Definition break_match {A : Set} : M A :=
  raise Exception.BreakMatch.

Definition panic {A : Set} (message : Coq.Strings.String.string) : M A :=
  raise (Exception.Panic message).

Definition call {A : Set} (e : M A) : M A :=
  LowM.Call e LowM.Pure.

Definition alloc {A : Set} (v : A) : M (Ref A) :=
  let- ref := LowM.CallPrimitive (Primitive.StateAlloc v) LowM.Pure in
  LowM.Pure (inl ref).

Definition read {A : Set} (r : Ref A) : M A :=
  match r with
  | Ref.Null => LowM.Impossible
  | Ref.Imm v => LowM.Pure (inl v)
  | Ref.MutRef address projection _ =>
    let- full_v := LowM.CallPrimitive (Primitive.StateRead address) LowM.Pure in
    match projection full_v with
    | None => LowM.Impossible
    | Some v => LowM.Pure (inl v)
    end
  end.

Definition write {A : Set} (r : Ref A) (v : A) : M unit :=
  match r with
  | Ref.Null => LowM.Impossible
  | Ref.Imm _ => LowM.Impossible
  | Ref.MutRef address _ injection =>
    let- full_v := LowM.CallPrimitive (Primitive.StateRead address) LowM.Pure in
    match injection v full_v with
    | None => LowM.Impossible
    | Some full_v' =>
      let- _ := LowM.CallPrimitive (Primitive.StateWrite address full_v') LowM.Pure in
      LowM.Pure (inl tt)
    end
  end.

Definition copy {A : Set} (r : Ref A) : M (Ref A) :=
  let* v := read r in
  alloc v.

Definition read_env {Env : Set} : M Env :=
  let- env := LowM.CallPrimitive Primitive.EnvRead LowM.Pure in
  LowM.Pure (inl env).

Definition impossible {A : Set} : M A :=
  LowM.Impossible.

(** Used for the definitions of "const". *)
(* @TODO: Give a definition for [run]. There should be an additional parameter
   witnessing that the calculation is possible. *)
Parameter run : forall {A : Set}, M A -> A.

Definition Val (A : Set) : Set := Ref A.

Definition catch {A : Set} (body : M A) (handler : Exception -> M A) : M A :=
  let- result := body in
  match result with
  | inl v => LowM.Pure (inl v)
  | inr exception => handler exception
  end.

Definition catch_return {A : Set} (body : M A) : M A :=
  catch
    body
    (fun exception =>
      match exception with
      | Exception.Return r => cast r
      | _ => raise exception
      end
    ).

Definition catch_continue (body : M (Val unit)) : M (Val unit) :=
  catch
    body
    (fun exception =>
      match exception with
      | Exception.Continue => alloc tt
      | _ => raise exception
      end
    ).

Definition catch_break (body : M (Val unit)) : M (Val unit) :=
  catch
    body
    (fun exception =>
      match exception with
      | Exception.Break => alloc tt
      | _ => raise exception
      end
    ).

Definition loop (body : M (Val unit)) : M (Val unit) :=
  LowM.Loop
    (catch_continue body)
    (fun result =>
      match result with
      | inl _ => false
      | inr _ => true
      end)
    (fun result =>
      catch_break (LowM.Pure result)).

Fixpoint match_operator {A B : Set}
    (scrutinee : A)
    (arms : list (A -> M B)) :
    M B :=
  match arms with
  | nil => impossible
  | arm :: arms =>
    catch
      (arm scrutinee)
      (fun exception =>
        match exception with
        | Exception.BreakMatch => match_operator scrutinee arms
        | _ => raise exception
        end
      )
  end.
