(** * The definition of a Rust monad. *)
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

(* Proof libraries that we can use everywhere. *)
Require Export Lia.
From Hammer Require Export Tactics.

Import List.ListNotations.

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

Module Ty.
  Parameter t : Set.

  Parameter path : string -> t.

  Parameter apply : t -> list t -> t.

  Parameter function : list t -> t -> t.

  Parameter tuple : list t -> t.

  (** As parameter: a list of traits, described by their absolute name and their
      list of type parameters, excluding `Self`. *)
  Parameter dyn : list (string * list t) -> t.

  (** This primitive is for associated types; it will require additional
      parameters. *)
  Parameter associated : t.
End Ty.

Module List.
  Fixpoint assoc {A : Set} (l : list (string * A)) (key : string) : option A :=
    match l with
    | [] => None
    | (k, v) :: l =>
      if String.eqb k key then
        Some v
      else
        assoc l key
    end.

  Fixpoint assoc_replace {A : Set}
      (l : list (string * A)) (key : string) (update : A) :
      list (string * A) :=
    match l with
    | [] => []
    | (k, v) :: l =>
      if String.eqb k key then
        (key, update) :: l
      else
        (k, v) :: assoc_replace l key update
    end.

  (** Update the list at the position given by [index]. Note that we silently
      fail in case the index is out of bounds. *)
  Fixpoint replace_at {A : Set} (l : list A) (index : nat) (update : A) :
      list A :=
    match l with
    | [] => []
    | x :: l =>
      match index with
      | O => update :: l
      | S index => x :: replace_at l index update
      end
    end.
End List.

Module Integer.
  Inductive t : Set :=
  | I8 : t
  | I16 : t
  | I32 : t
  | I64 : t
  | I128 : t
  | Isize : t
  | U8 : t
  | U16 : t
  | U32 : t
  | U64 : t
  | U128 : t
  | Usize : t.
End Integer.

Module Pointer.
  Module Index.
    (** We are very explicit for the indexes, so that if the target is mutated
        and the index does not make any sense anymore we can detect it. This
        can happen with unsafe code and enums for example, where the enum case
        might not be the correct one anymore. In that case, we want the
        semantics of the dereferencing to block the evaluation rather than to
        return an invalid field. *)
    Inductive t : Set :=
    | Tuple (index : Z)
    | Array (index : Z)
    | StructRecord (constructor field : string)
    | StructTuple (constructor : string) (index : Z).
  End Index.

  Module Path.
    Definition t : Set := list Index.t.
  End Path.

  Inductive t (Value : Set) : Set :=
  | Immediate (value : Value)
  | Mutable {Address : Set} (address : Address) (path : Path.t).
  Arguments Immediate {_}.
  Arguments Mutable {_ _}.
End Pointer.

Module Value.
  Inductive t : Set :=
  | Bool : bool -> t
  | Integer : Integer.t -> Z -> t
  (** For now we do not know how to represent floats so we use a string *)
  | Float : string -> t
  | UnicodeChar : Z -> t
  | String : string -> t
  | Tuple : list t -> t
  | Array : list t -> t
  | StructRecord : string -> list (string * t) -> t
  | StructTuple : string -> list t -> t
  | Pointer : Pointer.t t -> t
  (** The two existential types of the closure must be [Value.t] and [M]. We
      cannot enforce this constraint there yet, but we will do when defining the
      semantics. *)
  | Closure : {'(t, M) : Set * Set @ list t -> M} -> t
  (** A special value that does not appear in the translation, but that we use
      to implement primitive functions over values that are not total. We
      statically know, from the fact that the source Rust code is well-typed,
      that these error values are impossible. In these values appear in a proof,
      this might indicate invalid pre-conditions or mistakes in the translation
      to Coq. *)
  | Error (message : string)
  (** To implement the ability to declare a variable but not give it a value
      yet. *)
  | DeclaredButUndefined.

  (** Read the part of the value that is at a given pointer path, starting from
      the main value. It might return [None] if the path does not have a shape
      compatible with the value. *)
  Fixpoint read_path (value : Value.t) (path : Pointer.Path.t) :
      option Value.t :=
    match path with
    | [] => Some value
    | Pointer.Index.Tuple index :: path =>
      match value with
      | Tuple fields =>
        match List.nth_error fields (Z.to_nat index) with
        | Some value => read_path value path
        | None => None
        end
      | _ => None
      end
    | Pointer.Index.Array index :: path =>
      match value with
      | Array fields =>
        match List.nth_error fields (Z.to_nat index) with
        | Some value => read_path value path
        | None => None
        end
      | _ => None
      end
    | Pointer.Index.StructRecord constructor field :: path =>
      match value with
      | StructRecord c fields =>
        if String.eqb c constructor then
          match List.assoc fields field with
          | Some value => read_path value path
          | None => None
          end
        else
          None
      | _ => None
      end
    | Pointer.Index.StructTuple constructor index :: path =>
      match value with
      | StructTuple c fields =>
        if String.eqb c constructor then
          match List.nth_error fields (Z.to_nat index) with
          | Some value => read_path value path
          | None => None
          end
        else
          None
      | _ => None
      end
    end.

  (** Update the part of a value at a certain [path], and return [None] if the
      path is of invalid shape. *)
  Fixpoint write_value
      (value : Value.t) (path : Pointer.Path.t) (update : Value.t) :
      option Value.t :=
    match path with
    | [] => Some update
    | Pointer.Index.Tuple index :: path =>
      match value with
      | Tuple fields =>
        match List.nth_error fields (Z.to_nat index) with
        | Some value =>
          match write_value value path update with
          | Some value =>
            Some (Tuple (List.replace_at fields (Z.to_nat index) value))
          | None => None
          end
        | None => None
        end
      | _ => None
      end
    | Pointer.Index.Array index :: path =>
      match value with
      | Array fields =>
        match List.nth_error fields (Z.to_nat index) with
        | Some value =>
          match write_value value path update with
          | Some value =>
            Some (Array (List.replace_at fields (Z.to_nat index) value))
          | None => None
          end
        | None => None
        end
      | _ => None
      end
    | Pointer.Index.StructRecord constructor field :: path =>
      match value with
      | StructRecord c fields =>
        if String.eqb c constructor then
          match List.assoc fields field with
          | Some value =>
            match write_value value path update with
            | Some value =>
              Some (StructRecord c (List.assoc_replace fields field value))
            | None => None
            end
          | None => None
          end
        else
          None
      | _ => None
      end
    | Pointer.Index.StructTuple constructor index :: path =>
      match value with
      | StructTuple c fields =>
        if String.eqb c constructor then
          match List.nth_error fields (Z.to_nat index) with
          | Some value =>
            match write_value value path update with
            | Some value =>
              Some (StructTuple c (List.replace_at fields (Z.to_nat index) value))
            | None => None
            end
          | None => None
          end
        else
          None
      | _ => None
      end
    end.

  (** Equality between values. Defined only for basic types. *)
  Definition eqb (v1 v2 : Value.t) : bool :=
    match v1, v2 with
    | Value.Bool b1, Value.Bool b2 => Bool.eqb b1 b2
    | Value.Integer _ i1, Value.Integer _ i2 => Z.eqb i1 i2
    | Value.Float f1, Value.Float f2 => String.eqb f1 f2
    | Value.UnicodeChar c1, Value.UnicodeChar c2 => Z.eqb c1 c2
    | Value.String s1, Value.String s2 => String.eqb s1 s2
    | Value.Tuple _, Value.Tuple _
      | Value.Array _, Value.Array _
      | Value.StructRecord _ _, Value.StructRecord _ _
      | Value.StructTuple _ _, Value.StructTuple _ _
      | Value.Pointer _, Value.Pointer _
      | Value.Closure _, Value.Closure _
      | Value.Error _, Value.Error _
      | Value.DeclaredButUndefined, Value.DeclaredButUndefined =>
      true
    | _, _ => false
    end.

  Lemma eqb_is_reflexive (v : Value.t) : eqb v v = true.
  Proof.
    destruct v; simpl;
      try reflexivity;
      try apply Z.eqb_refl;
      try apply String.eqb_refl.
    now destruct_all bool.
  Qed.
End Value.

Module Primitive.
  Inductive t : Set :=
  | StateAlloc (value : Value.t)
  | StateRead {Address : Set} (address : Address)
  | StateWrite {Address : Set} (address : Address) (value : Value.t)
  | EnvRead
  | GetFunction (path : string) (generic_tys : list Ty.t)
  | GetAssociatedFunction (ty : Ty.t) (name : string) (generic_tys : list Ty.t)
  | GetTraitMethod
    (trait : string)
    (self_ty : Ty.t)
    (trait_tys : list Ty.t)
    (method : string)
    (generic_tys : list Ty.t).
End Primitive.

Module LowM.
  Inductive t (A : Set) : Set :=
  | Pure (value : A)
  | CallPrimitive (primitive : Primitive.t) (k : Value.t -> t A)
  | CallClosure (closure : Value.t) (args : list Value.t) (k : A -> t A)
  | Loop (body : t A) (k : A -> t A)
  | Impossible.
  Arguments Pure {_}.
  Arguments CallPrimitive {_}.
  Arguments CallClosure {_}.
  Arguments Loop {_}.
  Arguments Impossible {_}.

  Fixpoint let_ {A : Set} (e1 : t A) (e2 : A -> t A) : t A :=
    match e1 with
    | Pure v => e2 v
    | CallPrimitive primitive k =>
      CallPrimitive primitive (fun v => let_ (k v) e2)
    | CallClosure f args k =>
      CallClosure f args (fun v => let_ (k v) e2)
    | Loop body k =>
      Loop body (fun v => let_ (k v) e2)
    | Impossible => Impossible
    end.
End LowM.

Module Exception.
  Inductive t : Set :=
  (** exceptions for Rust's `return` *)
  | Return : Value.t -> t
  (** exceptions for Rust's `continue` *)
  | Continue : t
  (** exceptions for Rust's `break` *)
  | Break : t
  (** escape from a match branch once we know that it is not valid *)
  | BreakMatch : t
  | Panic : string -> t.
End Exception.

Definition M : Set :=
  LowM.t (Value.t + Exception.t).

Definition pure (v : Value.t) : M :=
  LowM.Pure (inl v).

Definition let_ (e1 : M) (e2 : Value.t -> M) : M :=
  LowM.let_ e1 (fun v1 =>
  match v1 with
  | inl v1 => e2 v1
  | inr error => LowM.Pure (inr error)
  end).

Module InstanceField.
  Inductive t : Set :=
  | Constant (constant : Value.t)
  | Method (method : list Ty.t -> list Value.t -> M)
  | Ty (ty : Ty.t).
End InstanceField.

Module Instance.
  Definition t : Set := list (string * InstanceField.t).
End Instance.

Parameter IsTraitInstance :
  forall
    (trait_name : string)
    (Self : Ty.t)
    (generic_tys : list Ty.t)
    (instance : Instance.t),
  Prop.

Parameter IsAssociatedFunction :
  forall
    (Self : Ty.t)
    (function_name : string)
    (function : list Ty.t -> list Value.t -> M),
  Prop.

Parameter IsAssociatedConstant :
  forall
    (Self : Ty.t)
    (constant_name : string)
    (constant : Value.t),
  Prop.

Parameter IsProvidedMethod :
  forall
    (trait_name : string)
    (method_name : string)
    (method : Ty.t -> list Ty.t -> list Value.t -> M),
  Prop.

Module Option.
  Definition bind {A B : Set} (x : option A) (f : A -> option B) : option B :=
    match x with
    | Some x => f x
    | None => None
    end.
End Option.

(** This parameter is used as a marker to allow a monadic notation
    without naming all intermediate results. Computation represented using
    this markers can be translated to a regular monadic computation using
    [M.monadic] tactic. Additionally, this parameter is used for the
    definitions of "const".*)
Parameter run : M -> Value.t.

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
    | M => exact e
    | _ => exact (pure e)
    end
  end.

Definition raise (exception : Exception.t) : M :=
  LowM.Pure (inr exception).

Definition return_ (r : Value.t) : M :=
  raise (Exception.Return r).

Definition continue : M :=
  raise Exception.Continue.

Definition break : M :=
  raise Exception.Break.

Definition break_match : M :=
  raise Exception.BreakMatch.

Definition panic (message : string) : M :=
  raise (Exception.Panic message).

Definition call_closure (f : Value.t) (args : list Value.t) : M :=
  LowM.CallClosure f args LowM.Pure.

Definition call_primitive (primitive : Primitive.t) : M :=
  LowM.CallPrimitive primitive (fun result =>
  LowM.Pure (inl result)).

Definition alloc (v : Value.t) : M :=
  call_primitive (Primitive.StateAlloc v).

Definition read (r : Value.t) : M :=
  match r with
  | Value.Pointer (Pointer.Immediate v) => LowM.Pure (inl v)
  | Value.Pointer (Pointer.Mutable address path) =>
    let* v := call_primitive (Primitive.StateRead address) in
    match Value.read_path v path with
    | Some v => LowM.Pure (inl v)
    | None => LowM.Impossible
    end
  | _ => LowM.Impossible
  end.

Definition write (r : Value.t) (update : Value.t) : M :=
  match r with
  | Value.Pointer (Pointer.Immediate _) => LowM.Impossible
  | Value.Pointer (Pointer.Mutable address path) =>
    let* value := call_primitive (Primitive.StateRead address) in
    match Value.write_value value path update with
    | Some value => call_primitive (Primitive.StateWrite address value)
    | None => LowM.Impossible
    end
  | _ => LowM.Impossible
  end.

Definition copy (r : Value.t) : M :=
  let* v := read r in
  alloc v.

Definition read_env : M :=
  call_primitive Primitive.EnvRead.

Definition impossible : M :=
  LowM.Impossible.

Parameter get_constant : string -> M.

Definition get_function (path : string) (generic_tys : list Ty.t) : M :=
  call_primitive (Primitive.GetFunction path generic_tys).

Definition get_associated_function
  (ty : Ty.t)
  (name : string)
  (generic_tys : list Ty.t) :
  M :=
  call_primitive (Primitive.GetAssociatedFunction ty name generic_tys).

Definition get_trait_method
    (trait : string)
    (self_ty : Ty.t)
    (trait_tys : list Ty.t)
    (method : string)
    (generic_tys : list Ty.t) :
    M :=
  call_primitive (Primitive.GetTraitMethod
    trait self_ty trait_tys method generic_tys
  ).

Definition catch (body : M) (handler : Exception.t -> M) : M :=
  let- result := body in
  match result with
  | inl v => LowM.Pure (inl v)
  | inr exception => handler exception
  end.

Definition catch_return (body : M) : M :=
  catch
    body
    (fun exception =>
      match exception with
      | Exception.Return r => pure r
      | _ => raise exception
      end
    ).

Definition catch_continue (body : M) : M :=
  catch
    body
    (fun exception =>
      match exception with
      | Exception.Continue => alloc (Value.Tuple [])
      | _ => raise exception
      end
    ).

Definition catch_break (body : M) : M :=
  catch
    body
    (fun exception =>
      match exception with
      | Exception.Break => alloc (Value.Tuple [])
      | _ => raise exception
      end
    ).

Definition loop (body : M) : M :=
  LowM.Loop
    (catch_continue body)
    (fun result =>
      catch_break (LowM.Pure result)).

Fixpoint match_operator
    (scrutinee : Value.t)
    (arms : list (Value.t -> M)) :
    M :=
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

(** Each arm must return a tuple of the free variables found in the pattern. If
    no arms are valid, we raise an [Exception.BreakMatch]. *)
Fixpoint find_or_pattern_aux
    (scrutinee : Value.t)
    (arms : list (Value.t -> M)) :
    M :=
  match arms with
  | nil => break_match
  | arm :: arms =>
    catch
      (arm scrutinee)
      (fun exception =>
        match exception with
        | Exception.BreakMatch => find_or_pattern_aux scrutinee arms
        | _ => raise exception
        end
      )
  end.

(** The [body] must be a closure. *)
Definition find_or_pattern
    (scrutinee : Value.t)
    (arms : list (Value.t -> M))
    (body : Value.t) :
    M :=
  let* free_vars := find_or_pattern_aux scrutinee arms in
  match free_vars with
  | Value.Tuple free_vars => call_closure body free_vars
  | _ => impossible
  end.

Definition never_to_any (x : Value.t) : M :=
  M.impossible.

Definition use (x : Value.t) : Value.t :=
  x.

(** An error should not occur as we statically know the number of fields in a
    tuple, but the code for the error branch is still there for typing and
    debugging reasons. *)
Definition get_tuple_field (value : Value.t) (index : Z) : Value.t :=
  match value with
  | Value.Pointer pointer =>
    match pointer with
    | Pointer.Immediate value =>
      match value with
      | Value.Tuple fields =>
        match List.nth_error fields (Z.to_nat index) with
        | Some field => Value.Pointer (Pointer.Immediate field)
        | None => Value.Error "invalid tuple index"
        end
      | _ => Value.Error "expected a tuple"
      end
    | Pointer.Mutable address path =>
      let new_path := path ++ [Pointer.Index.Tuple index] in
      Value.Pointer (Pointer.Mutable address new_path)
    end
  | _ => Value.Error "expected an address"
  end.

(** This function might fail, in case the [index] is out of range. *)
Definition get_array_field (value : Value.t) (index : Value.t) : M :=
  let* index := read index in
  match index with
  | Value.Integer Integer.Usize index =>
    match value with
    | Value.Pointer pointer =>
      match pointer with
      | Pointer.Immediate value =>
        match value with
        | Value.Array fields =>
          (* As this is in `usize`, the index is necessarily positive. *)
          match List.nth_error fields (Z.to_nat index) with
          | Some field => pure (Value.Pointer (Pointer.Immediate field))
          | None => panic "invalid array index"
          end
        | _ => pure (Value.Error "expected an array")
        end
      | Pointer.Mutable address path =>
        let new_path := path ++ [Pointer.Index.Array index] in
        pure (Value.Pointer (Pointer.Mutable address new_path))
      end
    | _ => pure (Value.Error "expected an address")
    end
  | _ => pure (Value.Error "Expected a usize as an array index")
  end.

(** Same as for [get_tuple_field], an error should not occur. *)
Definition get_struct_tuple_field
    (value : Value.t) (constructor : string) (index : Z) :
    Value.t :=
  match value with
  | Value.Pointer pointer =>
    match pointer with
    | Pointer.Immediate value =>
      match value with
      | Value.StructTuple current_constructor fields =>
        if String.eqb current_constructor constructor then
          match List.nth_error fields (Z.to_nat index) with
          | Some value => Value.Pointer (Pointer.Immediate value)
          | None => Value.Error "field not found"
          end
        else
          Value.Error "different values of constructor"
      | _ => Value.Error "not a struct tuple"
      end
    | Pointer.Mutable address path =>
      let new_path := path ++ [Pointer.Index.StructTuple constructor index] in
      Value.Pointer (Pointer.Mutable address new_path)
    end
  | _ => Value.Error "expected an address"
  end.

(** Same as for [get_tuple_field], an error should not occur. *)
Definition get_struct_record_field
    (value : Value.t) (constructor field : string) :
    Value.t :=
  match value with
  | Value.Pointer (Pointer.Immediate value) =>
    match value with
    | Value.StructRecord current_constructor fields =>
      if String.eqb current_constructor constructor then
        match List.assoc fields field with
        | Some value => Value.Pointer (Pointer.Immediate value)
        | None => Value.Error "field not found"
        end
      else
        Value.Error "different values of constructor"
    | _ => Value.Error "not a struct record"
    end
  | Value.Pointer (Pointer.Mutable address path) =>
    let new_path := path ++ [Pointer.Index.StructRecord constructor field] in
    Value.Pointer (Pointer.Mutable address new_path)
  | _ => Value.Error "expected an address"
  end.

Parameter pointer_coercion : Value.t -> Value.t.

Parameter assign : Value.t -> Value.t -> M.

Definition get_struct_tuple_field_or_break_match
    (value : Value.t) (constructor : string) (index : Z) :
    M :=
  match value with
  | Value.Pointer pointer =>
    match pointer with
    | Pointer.Immediate value =>
      match value with
      | Value.StructTuple current_constructor fields =>
        if String.eqb current_constructor constructor then
          match List.nth_error fields (Z.to_nat index) with
          | Some value => pure (Value.Pointer (Pointer.Immediate value))
          | None => M.impossible
          end
        else
          break_match
      | _ => M.impossible
      end
    | Pointer.Mutable address path =>
      match Value.read_path value path with
      | None => M.impossible
      | Some value =>
        match value with
        | Value.StructTuple current_constructor fields =>
          if String.eqb current_constructor constructor then
            let new_path :=
              path ++ [Pointer.Index.StructTuple constructor index] in
            pure (Value.Pointer (Pointer.Mutable address new_path))
          else
            break_match
        | _ => M.impossible
        end
      end
    end
  | _ => M.impossible
  end.

Definition get_struct_record_field_or_break_match
    (value : Value.t) (constructor field : string) :
    M :=
  match value with
  | Value.Pointer pointer =>
    match pointer with
    | Pointer.Immediate value =>
      match value with
      | Value.StructRecord current_constructor fields =>
        if String.eqb current_constructor constructor then
          match List.assoc fields field with
          | Some value => pure (Value.Pointer (Pointer.Immediate value))
          | None => M.impossible
          end
        else
          break_match
      | _ => M.impossible
      end
    | Pointer.Mutable address path =>
      match Value.read_path value path with
      | None => M.impossible
      | Some value =>
        match value with
        | Value.StructRecord current_constructor fields =>
          if String.eqb current_constructor constructor then
            let new_path :=
              path ++ [Pointer.Index.StructRecord constructor field] in
            pure (Value.Pointer (Pointer.Mutable address new_path))
          else
            break_match
        | _ => M.impossible
        end
      end
    end
  | _ => M.impossible
  end.

Definition is_constant_or_break_match (value expected_value : Value.t) : M :=
  if Value.eqb value expected_value then
    pure (Value.Tuple [])
  else
    break_match.

(** Get an element of a slice by index. *)
Parameter get_slice_index_or_break_match :
  Value.t -> Z -> M.

(** Get an element of a slice by index counting from the end. *)
Parameter get_slice_rev_index_or_break_match :
  Value.t -> Z -> M.

(** For two indices n and k, get all elements of a slice without
    the first n elements and without the last k elements. *)
Parameter get_slice_rest_or_break_match :
  Value.t -> Z -> Z -> M.

(** This function is explicitely called in the Rust AST, and should take two
    types that are actually different but convertible, like different kinds of
    integers. *)
Parameter rust_cast : Value.t -> Value.t.

Definition closure (f : list Value.t -> M) : Value.t :=
  Value.Closure (existS (Value.t, M) f).

Definition constructor_as_closure (constructor : string) : Value.t :=
  closure (fun args =>
    pure (Value.StructTuple constructor args)).

Parameter struct_record_update : Value.t -> list (string * Value.t) -> Value.t.
