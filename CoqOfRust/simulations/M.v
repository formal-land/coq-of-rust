Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

(** ** Monads that are useful for the definition of simulations. *)

Module Result.
  Inductive t (A Error : Set) : Set :=
  | Ok : A -> t A Error
  | Err : Error -> t A Error.

  Arguments Ok {A Error}%_type_scope.
  Arguments Err {A Error}%_type_scope.

  Definition return_ {A Error : Set} (value : A) : t A Error := Ok value.

  Definition bind {Error A B : Set} (value : t A Error) (f : A -> t B Error) : t B Error :=
    match value with
    | Ok value => f value
    | Err error => Err error
    end.

  Definition fold_left {A B Error : Set} (init : A) (l : list B) (f : A -> B -> t A Error) :
      t A Error :=
    List.fold_left (fun acc x => bind acc (fun acc => f acc x)) l (return_ init).

  Module List.
    Definition map {A B Error : Set} (f : A -> t B Error) :=
      fix fixpoint (l : list A) : t (list B) Error :=
        match l with
        | [] => return_ []
        | x :: l =>
          bind (f x) (fun y => bind (fixpoint l) (fun ys => return_ (y :: ys)))
        end.
  End List.
End Result.

Module ResultNotations.
  (** The type contained by the monad is always the last one, so we reverse the order of
      parameters. *)
  Notation "M?" := (fun A Error => Result.t Error A).

  Notation "return?" := Result.return_.

  Notation "'let?' x ':=' X 'in' Y" :=
    (Result.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "fold?" := Result.fold_left.
End ResultNotations.

Module Panic.
  Inductive t (A : Set) : Set :=
  | Value : A -> t A
  (** The [Panic] works with an existential type, so we can return any payload for errors. This is
      useful for debugging. Then we cannot catch the error and compute with it as we do not know the
      type anymore, but catching panic errors is not supposed to happen in Rust. *)
  | Panic : {Error : Set @ Error} -> t A.
  Arguments Value {_}.
  Arguments Panic {_}.

  Definition return_ {A : Set} (value : A) : t A :=
    Value value.
  Arguments return_ /.

  Definition panic {A Error : Set} (error : Error) : t A :=
    Panic (existS Error error).

  Definition bind {A B : Set} (value : t A) (f : A -> t B) : t B :=
    match value with
    | Value value => f value
    | Panic error => Panic error
    end.

  Definition fold_left {A B : Set} (init : A) (l : list B) (f : A -> B -> t A) : t A :=
    List.fold_left (fun acc x => bind acc (fun acc => f acc x)) l (return_ init).

  Definition map {A B : Set} (l : list A) (f : A -> t B) : t (list B) :=
    List.fold_right
      (fun x acc => bind acc (fun acc => bind (f x) (fun x => return_ (x :: acc))))
      (return_ []) l.

  Module List.
    Definition nth {A : Set} (l : list A) (n : nat) : t A :=
      match List.nth_error l n with
      | Some value => return_ value
      | None => panic "List.nth: index out of bounds"
      end.
  End List.
End Panic.

Module PanicNotations.
  Notation "M!" := Panic.t.

  Notation "return!" := Panic.return_.
  Notation "panic!" := Panic.panic.

  Notation "'let!' x ':=' X 'in' Y" :=
    (Panic.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "'do!' X 'in' Y" :=
    (Panic.bind X (fun (_ : unit) => Y))
    (at level 200, X at level 100, Y at level 200).

  Notation "fold!" := Panic.fold_left.

  Notation "map!" := Panic.map.
End PanicNotations.

Module PanicResult.
  Import PanicNotations.

  Definition t (Error A : Set) : Set := Panic.t (Result.t A Error).

  Definition return_ {Error A : Set} (value : A) : t Error A :=
    return! (Result.Ok value).

  Definition bind {Error A B : Set} (value : t Error A) (f : A -> t Error B) : t Error B :=
    let! value := value in
    match value with
    | Result.Ok value => f value
    | Result.Err error => return! (Result.Err error)
    end.
End PanicResult.

Module PanicResultNotations.
  Notation "M!?" := PanicResult.t.

  Notation "return!?" := PanicResult.return_.

  Notation "'let!?' x ':=' X 'in' Y" :=
    (PanicResult.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).
End PanicResultNotations.

Module State.
  Definition t (State A : Set) : Set := State -> A * State.

  Definition return_ {State A : Set} (value : A) : t State A :=
    fun state => (value, state).

  Definition bind {State A B : Set} (value : t State A) (f : A -> t State B) : t State B :=
    fun state =>
      let (value, state) := value state in
      f value state.

  (** Same as [List.fold_left] but for functions that return a monadic value. We use the order of
      parameters from the `for` operator, with initialization first, the remaining elements, and then
      the body of the loop. The idea is to look similar to the source code. *)
  Definition fold_left {State A B : Set} (init : A) (l : list B) (f : A -> B -> t State A) :
      t State A :=
    List.fold_left (fun acc x => bind acc (fun acc => f acc x)) l (return_ init).

  Definition read {State : Set} : t State State :=
    fun state => (state, state).

  Definition write {State : Set} (state : State) : t State unit :=
    fun _ => (tt, state).
End State.

Module StateNotations.
  Notation "'MS" := State.t.

  Notation "'returnS" := State.return_.

  Notation "'letS' x ':=' X 'in' Y" :=
    (State.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "'foldS" := State.fold_left.

  Notation "'readS" := State.read.

  Notation "'writeS" := State.write.
End StateNotations.

Module StatePanic.
  Import PanicNotations.

  (** In case of panic, we discard the return state. *)
  Definition t (State A : Set) : Set := State -> Panic.t (A * State).

  Definition return_ {State A : Set} (value : A) : t State A :=
    fun state => return! (value, state).

  Definition bind {State A B : Set} (value : t State A) (f : A -> t State B) : t State B :=
    fun state =>
      let! (value, state) := value state in
      f value state.

  (** Same as [List.fold_left] but for functions that return a monadic value. We use the order of
      parameters from the `for` operator, with initialization first, the remaining elements, and then
      the body of the loop. The idea is to look similar to the source code. *)
  Definition fold_left {State A B : Set} (init : A) (l : list B) (f : A -> B -> t State A) :
      t State A :=
    List.fold_left (fun acc x => bind acc (fun acc => f acc x)) l (return_ init).

  Definition read {State : Set} : t State State :=
    fun state => return! (state, state).

  Definition write {State : Set} (state : State) : t State unit :=
    fun _ => return! (tt, state).

  (** We also put the current [state] in the panic message. *)
  Definition panic {State Error A : Set} (err : Error) : t State A :=
    fun state => panic! (err, state).

  Definition lift_from_panic {State A : Set} (value : M! A) : t State A :=
    fun state =>
      let! value := value in
      return! (value, state).

  (** Use a value of type [Borrowed] to initialize a new part of the state, and return it at the
      end. *)
  Definition borrow {Big_State State Borrowed A : Set}
      (take : State -> Big_State) (give_back : Big_State -> State * Borrowed)
      (value : t Big_State A) :
      t State (A * Borrowed) :=
    fun state =>
      let big_state := take state in
      let! (value, big_state) := value big_state in
      let (state, borrowed) := give_back big_state in
      return! ((value, borrowed), state).
End StatePanic.

Module StatePanicNotations.
  Notation "MS!" := StatePanic.t.

  Notation "returnS!" := StatePanic.return_.

  Notation "'letS!' x ':=' X 'in' Y" :=
    (StatePanic.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "readS!" := StatePanic.read.

  Notation "writeS!" := StatePanic.write.

  Notation "panicS!" := StatePanic.panic.

  Notation "return!toS!" := StatePanic.lift_from_panic.

  Notation "borrowS!" := StatePanic.borrow.

  Notation "foldS!" := StatePanic.fold_left.
End StatePanicNotations.

Module StatePanicResult.
  Import ResultNotations.
  Import PanicNotations.
  Import StatePanicNotations.

  Definition t (State Error A : Set) : Set :=
    MS! State (M? Error A).

  Definition return_ {State Error A : Set} (value : A) : t State Error A :=
    returnS! (Result.Ok value).

  Definition bind {State Error A B : Set}
      (value : t State Error A)
      (f : A -> t State Error B) :
      t State Error B :=
    fun (state : State) =>
    match value state with
    | Panic.Panic error => panic! error
    | Panic.Value (value, state) =>
      match value with
      | Result.Ok value => f value state
      | Result.Err error => Panic.Value (Result.Err error, state)
      end
    end.

  (** The order of parameters is the same as in the source `for` loops. *)
  Definition fold_left {State Error A B : Set}
      (init : A)
      (l : list B)
      (f : A -> B -> t State Error A) :
      t State Error A :=
    List.fold_left (fun acc x => bind acc (fun acc => f acc x)) l (return_ init).

  Definition lift_from_panic {State Error A : Set} (value : M! A) : t State Error A :=
    fun (state : State) =>
      match value with
      | Panic.Panic error => panic! error
      | Panic.Value value => return! (Result.Ok value, state)
      end.
End StatePanicResult.

Module StatePanicResultNotations.
  Notation "MS!?" := StatePanicResult.t.

  Notation "returnS!?" := StatePanicResult.return_.

  Notation "'letS!?' x ':=' X 'in' Y" :=
    (StatePanicResult.bind X (fun x => Y))
    (at level 200, x pattern, X at level 100, Y at level 200).

  Notation "'doS!?' X 'in' Y" :=
    (StatePanicResult.bind X (fun (_ : unit) => Y))
    (at level 200, X at level 100, Y at level 200).

  Notation "foldS!?" := StatePanicResult.fold_left.

  Notation "return!toS!?" := StatePanicResult.lift_from_panic.
End StatePanicResultNotations.

(** ** Lens that are useful for the definition of simulations. *)

Module Lens.
  Import PanicNotations.
  Import StatePanicNotations.

  Record t {Big_A A : Set} : Set := {
    read : Big_A -> A;
    write : Big_A -> A -> Big_A
  }.
  Arguments t : clear implicits.

  Definition lift {Big_State State A : Set}
      (lens : t Big_State State)
      (value : MS! State A) :
      MS! Big_State A :=
    fun big_state =>
      let! (value, state) := value (lens.(read) big_state) in
      return! (value, lens.(write) big_state state).
End Lens.

Module LensOption.
  Import PanicNotations.
  Import StatePanicNotations.

  Record t {Big_A A : Set} : Set := {
    read : Big_A -> option A;
    write : Big_A -> A -> option Big_A
  }.
  Arguments t : clear implicits.

  Definition of_lens {Big_A A : Set}
      (lens : Lens.t Big_A A) : t Big_A A :=
    {|
      read big_a := Some (lens.(Lens.read) big_a);
      write big_a a := Some (lens.(Lens.write) big_a a)
    |}.

  Definition lift {Big_State State A : Set}
      (lens : t Big_State State)
      (value : MS! State A) :
      MS! Big_State (option A) :=
    fun big_state =>
      match lens.(read) big_state with
      | Some result =>
        let! (value, state) := value result in
        match lens.(write) big_state state with
        | Some big_state => return! (Some value, big_state)
        | None => return! (None, big_state)
        end
      | None => return! (None, big_state)
      end.
End LensOption.

Module LensPanic.
  Import PanicNotations.
  Import StatePanicNotations.

  Record t {Big_A A : Set} : Set := {
    read : Big_A -> M! A;
    write : Big_A -> A -> M! Big_A
  }.
  Arguments t : clear implicits.

  Definition of_lens {Big_A A : Set}
      (lens : Lens.t Big_A A) : t Big_A A :=
    {|
      read big_a := return! (lens.(Lens.read) big_a);
      write big_a a := return! (lens.(Lens.write) big_a a)
    |}.

  Definition lift {Big_State State A : Set}
      (lens : t Big_State State)
      (value : MS! State A) :
      MS! Big_State A :=
    fun big_state =>
      let! state := lens.(read) big_state in
      let! (value, state) := value state in
      let! big_state := lens.(write) big_state state in
      return! (value, big_state).
End LensPanic.

Module LensConversions.
  Import PanicNotations.

  Definition panic_of_option {Big_State State}
      (x : LensOption.t Big_State State) :
      LensPanic.t Big_State State :=
    {|
      LensPanic.read big_state :=
        match x.(LensOption.read) big_state with
        | Some value => return! value
        | None => panic! ""
        end;
      LensPanic.write big_state state :=
        match x.(LensOption.write) big_state state with
        | Some value => return! value
        | None => panic! ""
        end
    |}.

  Definition option_of_panic {Big_State State}
      (x : LensPanic.t Big_State State) :
      LensOption.t Big_State State :=
    {|
      LensOption.read big_state :=
        match x.(LensPanic.read) big_state with
        | Panic.Value value => Some value
        | Panic.Panic _ => None
        end;
      LensOption.write big_state state :=
        match x.(LensPanic.write) big_state state with
        | Panic.Value value => Some value
        | Panic.Panic _ => None
        end
    |}.
End LensConversions.

Module LensNotations.
  Notation "liftS!" := Lens.lift.
  Notation "liftS!of?" := LensOption.lift.
  Notation "liftS!of!" := LensPanic.lift.

  Notation "lens_of?" := LensOption.of_lens.
  Notation "lens_of!" := LensPanic.of_lens.
  Notation "lens!of?" := LensConversions.panic_of_option.
  Notation "lens?of!" := LensConversions.option_of_panic.
End LensNotations.

Module Notations.
  Include ResultNotations.
  Include PanicNotations.
  Include PanicResultNotations.
  Include StateNotations.
  Include StatePanicNotations.
  Include StatePanicResultNotations.
  Include LensNotations.

  Notation "f $ x" := (f x) (at level 60, right associativity, only parsing).

  (** Convenient as the state monads hide the state variable which can be needed for reduction *)
  Ltac unfold_state_monad :=
    repeat (
      unfold StatePanicResult.bind, StatePanic.bind, StatePanic.bind,
        "returnS!",
        "return!toS!", 
        "liftS!", 
        "liftS!of?",
        "readS!", 
        "return!toS!?";
      cbn
    ).
End Notations.

Module Stack.
  Definition t : Type :=
    list Set.

  Fixpoint to_Set_aux (A : Set) (Stack : t) : Set :=
    match Stack with
    | [] => A
    | B :: Stack => A * to_Set_aux B Stack
    end.

  Definition to_Set (Stack : t) : Set :=
    match Stack with
    | [] => unit
    | A :: Stack => to_Set_aux A Stack
    end.

  Definition nth (Stack : t) (index : nat) : Set :=
    List.nth index Stack unit.

  Fixpoint read_aux {A : Set} {Stack : t}
    (stack : to_Set_aux A Stack)
    (index : nat)
    {struct Stack} :
    nth (A :: Stack) index.
  Proof.
    destruct Stack as [|B Stack], index as [|index]; cbn in *.
    { exact stack. }
    { destruct index; exact tt. }
    { exact (fst stack). }
    { exact (read_aux _ _ (snd stack) index). }
  Defined.

  Definition read {Stack : t} (stack : to_Set Stack) (index : nat) : nth Stack index.
  Proof.
    destruct Stack; cbn in *.
    { destruct index; exact tt. }
    { apply (read_aux stack). }
  Defined.

  Fixpoint write_aux {A : Set} {Stack : t}
    (stack : to_Set_aux A Stack)
    (index : nat)
    (value : nth (A :: Stack) index)
    {struct Stack} :
    to_Set_aux A Stack.
  Proof.
    destruct Stack as [|B Stack], index as [|index]; cbn in *.
    { exact value. }
    { exact stack. }
    { exact (value, snd stack). }
    { exact (fst stack, write_aux _ _ (snd stack) index value). }
  Defined.

  Definition write {Stack : t}
    (stack : to_Set Stack)
    (index : nat)
    (value : nth Stack index) :
    to_Set Stack.
  Proof.
    destruct Stack; cbn in *.
    { exact tt. }
    { apply (write_aux stack index value). }
  Defined.

  Fixpoint alloc_aux {A : Set} {Stack : t} {B : Set}
    (stack : to_Set_aux A Stack)
    (value : B)
    {struct Stack} :
    to_Set_aux A (Stack ++ [B]).
  Proof.
    destruct Stack as [|A' Stack]; cbn in *.
    { exact (stack, value). }
    { exact (fst stack, alloc_aux _ _ _ (snd stack) value). }
  Defined.

  Definition alloc {Stack : t} {A : Set} (stack : to_Set Stack) (value : A) :
    to_Set (Stack ++ [A]).
  Proof.
    destruct Stack; cbn in *.
    { exact value. }
    { apply (alloc_aux stack value). }
  Defined.

  Fixpoint dealloc_aux {A : Set} {Stack : t} {B : Set}
    (stack : to_Set_aux A (Stack ++ [B]))
    {struct Stack} :
    to_Set_aux A Stack * B.
  Proof.
    destruct Stack as [|A' Stack]; cbn in *.
    { exact stack. }
    { exact (
        let '(stack', value) := dealloc_aux _ _ _ (snd stack) in
        ((fst stack, stack'), value)
      ).
    }
  Defined.

  Definition dealloc {Stack : t} {A : Set} (stack : to_Set (Stack ++ [A])) : to_Set Stack * A.
  Proof.
    destruct Stack; cbn in *.
    { exact (tt, stack). }
    { exact (dealloc_aux stack). }
  Defined.

  Module CanAccess.
    Inductive t {A : Set} `{Link A} (Stack : Stack.t) : Ref.Core.t A -> Set :=
    | Immediate
        (value : option A) :
      t Stack (Ref.Core.Immediate value)
    | Mutable
        (index : nat)
        (path : Pointer.Path.t)
        (big_to_value : nth Stack index -> Value.t)
        (projection : nth Stack index -> option A)
        (injection : nth Stack index -> A -> option (nth Stack index)) :
      t Stack (Ref.Core.Mutable (Address := nat) (Big_A := nth Stack index)
          index path big_to_value projection injection
        ).

    Definition runner {Stack : Stack.t} {A : Set} `{Link A} {index : Pointer.Index.t}
        {ref_core : Ref.Core.t A}
        (runner : SubPointer.Runner.t A index)
        (H_ref_core : t Stack ref_core) :
      t Stack (SubPointer.Runner.apply ref_core runner).
    Proof.
      destruct H_ref_core.
      { apply Immediate. }
      { apply Mutable. }
    Defined.

    Definition read {A : Set} `{Link A} {Stack : Stack.t}
        {ref_core : Ref.Core.t A}
        (run : t Stack ref_core)
        (stack : to_Set Stack) :
        option A :=
      match run with
      | Immediate _ value => value
      | Mutable _ index _ _ projection _ => projection (read stack index)
      end.

    Definition write {A : Set} `{Link A} {Stack : Stack.t}
        {ref_core : Ref.Core.t A}
        (run : t Stack ref_core)
        (stack : to_Set Stack)
        (value : A) :
        option (to_Set Stack) :=
      match run with
      | Immediate _ _ => None
      | Mutable _ index _ _ _ injection =>
        match injection (Stack.read stack index) value with
        | Some value => Some (Stack.write stack index value)
        | None => None
        end
      end.
  End CanAccess.
End Stack.

Module Run.
  Reserved Notation "{{ StackIn 🌲 e }}".

  Inductive t {R Output : Set} (StackIn : Stack.t) : LowM.t R Output -> Set :=
  | Pure
      (output : Output.t R Output) :
    {{ StackIn 🌲 LowM.Pure output }}
  | StateAlloc {A : Set} `{Link A}
      (value : A)
      (k : Ref.Core.t A -> LowM.t R Output)
    (H_k :
      {{ StackIn ++ [A] 🌲
        let ref_core :=
          Ref.Core.Mutable
            (List.length StackIn)
            []
            φ
            Some
            (fun _ => Some) in
        k ref_core
      }}
    ) :
    {{ StackIn 🌲 LowM.CallPrimitive (Primitive.StateAlloc value) k }}
  | StateRead {A : Set} `{Link A}
      (ref_core : Ref.Core.t A)
      (k : A -> LowM.t R Output)
    (H_access : Stack.CanAccess.t StackIn ref_core)
    (H_k : forall (value : A),
      {{ StackIn 🌲 k value }}
    ) :
    {{ StackIn 🌲 LowM.CallPrimitive (Primitive.StateRead ref_core) k }}
  | StateWrite {A : Set} `{Link A}
      (ref_core : Ref.Core.t A)
      (value : A)
      (k : unit -> LowM.t R Output)
    (H_access : Stack.CanAccess.t StackIn ref_core)
    (H_k : {{ StackIn 🌲 k tt }}) :
    {{ StackIn 🌲 LowM.CallPrimitive (Primitive.StateWrite ref_core value) k }}
  | GetSubPointer {A : Set} `{Link A}
      (index : Pointer.Index.t)
      (ref_core : Ref.Core.t A)
      (runner : SubPointer.Runner.t A index)
      (k : Ref.Core.t runner.(SubPointer.Runner.Sub_A) -> LowM.t R Output)
    (H_k : {{ StackIn 🌲 k (SubPointer.Runner.apply ref_core runner) }}) :
    {{ StackIn 🌲 LowM.CallPrimitive (Primitive.GetSubPointer ref_core runner) k }}
  | Call {Output' : Set}
      (e : LowM.t Output' Output')
      (k : SuccessOrPanic.t Output' -> LowM.t R Output)
    (H_e : {{ [] 🌲 e }})
    (H_k : forall (output' : SuccessOrPanic.t Output'),
      {{ StackIn 🌲 k output' }}
    ) :
    {{ StackIn 🌲 LowM.Call e k }}
  | LetAlloc {Output' : Set} `{Link Output'}
      (e : LowM.t R Output')
      (k : Output.t R (Ref.t Pointer.Kind.Raw Output') -> LowM.t R Output)
    (H_e : {{ StackIn 🌲 e }})
    (H_k : forall (ref_or_exception : Output.t R (Ref.t Pointer.Kind.Raw Output')),
      let StackIn' :=
        match ref_or_exception with
        | Output.Success _ => StackIn ++ [Output']
        | Output.Exception _ => StackIn
        end in
      {{ StackIn' 🌲 k ref_or_exception }}
    ) :
    {{ StackIn 🌲 LowM.LetAlloc e k }}

  where "{{ StackIn 🌲 e }}" := (t StackIn e).
End Run.

Export Run.

Fixpoint evaluate {R Output : Set} {StackIn : Stack.t} {e : LowM.t R Output}
    (run : {{ StackIn 🌲 e }})
    (stack_in : Stack.to_Set StackIn)
    {struct run} :
  Output.t R Output * Stack.to_Set StackIn.
Proof.
  destruct run.
  { (* Pure *)
    exact (output, stack_in).
  }
  { (* StateAlloc *)
    refine (
      let '(output, stack_out) := _ in
      (output, fst (Stack.dealloc (A := A) stack_out))
    ).
    unshelve eapply (evaluate _ _ _ _ run _).
    exact (Stack.alloc stack_in value).
  }
  { (* StateRead *)
    destruct (Stack.CanAccess.read H_access stack_in) as [value|].
    { exact (evaluate _ _ _ _ (H_k value) stack_in). }
    { exact (Output.panic "StateRead: invalid reference", stack_in). }
  }
  { (* StateWrite *)
    destruct (Stack.CanAccess.write H_access stack_in value) as [stack_in'|].
    { exact (evaluate _ _ _ _ run stack_in'). }
    { exact (Output.panic "StateWrite: invalid reference", stack_in). }
  }
  { (* GetSubPointer *)
    exact (evaluate _ _ _ _ run stack_in).
  }
  { (* Call *)
    unshelve eapply (evaluate _ _ _ _ (H_k _) stack_in).
    apply SuccessOrPanic.of_output.
    apply (evaluate _ _ _ _ run tt).
  }
  { (* LetAlloc *)
    refine (
      let '(output', stack_in') := evaluate _ _ _ _ run stack_in in
      _
    ).
    destruct output' as [output' | exception].
    { refine (
        let ref_core :=
          Ref.Core.Mutable
            (List.length StackIn)
            []
            φ
            Some
            (fun _ => Some) in
        let ref : Ref.t Pointer.Kind.Raw Output' := {| Ref.core := ref_core |} in
        _
      ).
      refine (
        let '(output, stack_out) := _ in
        (output, fst (Stack.dealloc (A := Output') stack_out))
      ).
      unshelve eapply (evaluate _ _ _ _ (H_k (Output.Success ref)) _).
      exact (Stack.alloc stack_in' output').
    }
    { exact (evaluate _ _ _ _ (H_k (Output.Exception exception)) stack_in'). }
  }
Defined.
