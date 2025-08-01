(** * The definition of a Rust monad. *)
Require Export Coq.Strings.PrimString.
Require Export Coq.ZArith.ZArith.

(* Proof libraries that we can use everywhere. *)
Require Export Lia.
From Hammer Require Export Tactics.
Require Export smpl.Smpl.
Require Export coqutil.Datatypes.List.

Import List.ListNotations.
Import PStringNotations.

Local Open Scope list.
Local Open Scope pstring_scope.

(** Activate the handling of modulo in `lia`. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

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

Module List.
  Fixpoint assoc {A : Set} (l : list (string * A)) (key : string) : option A :=
    match l with
    | [] => None
    | (k, v) :: l =>
      match PrimString.compare k key with
      | Eq => Some v
      | _ => assoc l key
      end
    end.

  Fixpoint assoc_replace {A : Set}
      (l : list (string * A)) (key : string) (update : A) :
      list (string * A) :=
    match l with
    | [] => []
    | (k, v) :: l =>
      match PrimString.compare k key with
      | Eq => (key, update) :: l
      | _ => (k, v) :: assoc_replace l key update
      end
    end.

  (** Code taken from the standard library without the use of a functor and properties. *)
  Module Sort.
    Fixpoint merge {A : Set} (leb : A -> A -> bool) (l1 l2 : list A) : list A :=
      let fix merge_aux l2 :=
      match l1, l2 with
      | [], _ => l2
      | _, [] => l1
      | a1::l1', a2::l2' =>
          if leb a1 a2 then
            a1 :: merge leb l1' l2
          else
            a2 :: merge_aux l2'
      end
      in merge_aux l2.

    Fixpoint merge_list_to_stack {A : Set} (leb : A -> A -> bool) stack l :=
      match stack with
      | [] => [Some l]
      | None :: stack' => Some l :: stack'
      | Some l' :: stack' => None :: merge_list_to_stack leb stack' (merge leb l' l)
      end.

    Fixpoint merge_stack {A : Set} (leb : A -> A -> bool) stack :=
      match stack with
      | [] => []
      | None :: stack' => merge_stack leb stack'
      | Some l :: stack' => merge leb l (merge_stack leb stack')
      end.

    Fixpoint iter_merge {A : Set} (leb : A -> A -> bool) stack l :=
      match l with
      | [] => merge_stack leb stack
      | a::l' => iter_merge leb (merge_list_to_stack leb stack [a]) l'
      end.

    Definition sort {A : Set} (leb : A -> A -> bool) (l : list A) : list A :=
      iter_merge leb [] l.
  End Sort.

  Definition sort_assoc {A : Set} (l : list (string * A)) : list (string * A) :=
    let leb x y :=
      match PrimString.compare (fst x) (fst y) with
      | Lt | Eq => true
      | Gt => false
      end in
    Sort.sort leb l.

  Goal sort_assoc [("2", 2); ("1", 1); ("3", 3)] = [("1", 1); ("2", 2); ("3", 3)].
  Proof. reflexivity. Qed.

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

  Lemma replace_at_map_eq {A B : Set} (l : list A) (f : A -> B) (index : nat) (update : A) :
    List.map f (replace_at l index update) =
    replace_at (List.map f l) index (f update).
  Proof.
    revert l; induction index; intros; destruct l; cbn; f_equal; auto.
  Qed.
End List.

Module IntegerKind.
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

  Definition eqb (kind1 kind2 : t) : bool :=
    match kind1, kind2 with
    | I8, I8 => true
    | I16, I16 => true
    | I32, I32 => true
    | I64, I64 => true
    | I128, I128 => true
    | Isize, Isize => true
    | U8, U8 => true
    | U16, U16 => true
    | U32, U32 => true
    | U64, U64 => true
    | U128, U128 => true
    | Usize, Usize => true
    | _, _ => false
    end.
End IntegerKind.

Module Ty.
  Parameter t : Set.

  Parameter path : string -> Ty.t.

  Parameter function : list Ty.t -> Ty.t -> Ty.t.

  Parameter tuple : list Ty.t -> Ty.t.
End Ty.

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

  Module Core.
    Inductive t (Value : Set) : Set :=
    (** The immediate value is optional in case with have a sub-pointer of an immediate pointer for
        an enum case that is not the current one. *)
    | Immediate (value : option Value)
    | Mutable {Address : Set} (address : Address) (path : Path.t).
    Arguments Immediate {_}.
    Arguments Mutable {_ _}.
  End Core.

  Module Kind.
    Inductive t : Set :=
    (** The address kind for the allocation primitive. This is later converted to proper pointer
        kinds. This is not a native Rust kind of pointer. *)
    | Raw
    | Ref
    | MutRef
    | ConstPointer
    | MutPointer.

    Definition to_ty_path (kind : t) : string :=
      match kind with
      | Raw => "*"
      | Ref => "&"
      | MutRef => "&mut"
      | ConstPointer => "*const"
      | MutPointer => "*mut"
      end.
  End Kind.

  Record t {Value : Set} : Set := {
    kind : Kind.t;
    core : Core.t Value;
  }.
  Arguments t : clear implicits.

  Definition deref {Value : Set} (pointer : t Value) : t Value :=
    {|
      kind := Kind.Raw;
      core :=pointer.(core);
    |}.
End Pointer.

Module Value.
  Inductive t : Set :=
  | Bool : bool -> t
  | Integer (kind : IntegerKind.t) (z : Z) : t
  (** For now we do not know how to represent floats so we use a string *)
  | Float : string -> t
  | UnicodeChar : Z -> t
  | String : string -> t
  | Tuple : list t -> t
  | Array : list t -> t
  | StructRecord : string -> list t -> list Ty.t ->list (string * t) -> t
  | StructTuple : string -> list t -> list Ty.t -> list t -> t
  | Pointer : Pointer.t t -> t
  (** The two existential types of the closure must be [Value.t] and [M]. We
      cannot enforce this constraint there yet, but we will do when defining the
      semantics. *)
  | Closure : {'(Value, M) : (Set * Set) @ list Value -> M} -> t
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

  (** We use this smart constructor to ensure that the fields are sorted, and hence in a
      canonical form. We do not sort the fields in the source code as we must keep the order in
      which they are created, in case of side-effects. *)
  Definition mkStructRecord
      (constructor : string)
      (consts : list t)
      (tys : list Ty.t)
      (fields : list (string * t)) :
      t :=
    StructRecord constructor consts tys (List.sort_assoc fields).
  Arguments mkStructRecord /.

  (** Read the part of the value that is at a given pointer index. It might return [None] if the
      index does not have a shape compatible with the value. *)
  Definition read_index (value : Value.t) (index : Pointer.Index.t) : option Value.t :=
    match index with
    | Pointer.Index.Tuple index =>
      match value with
      | Tuple fields => List.nth_error fields (Z.to_nat index)
      | _ => None
      end
    | Pointer.Index.Array index =>
      match value with
      | Array fields => List.nth_error fields (Z.to_nat index)
      | _ => None
      end
    | Pointer.Index.StructRecord constructor field =>
      match value with
      | StructRecord c _ _ fields =>
        match PrimString.compare c constructor with
        | Eq => List.assoc fields field
        | _ => None
        end
      | _ => None
      end
    | Pointer.Index.StructTuple constructor index =>
      match value with
      | StructTuple c _ _ fields =>
        match PrimString.compare c constructor with
        | Eq => List.nth_error fields (Z.to_nat index)
        | _ => None
        end
      | _ => None
      end
    end.

  (** Update the part of a value at a certain [index], and return [None] if the index is of invalid
      shape. *)
  Definition write_index
      (value : Value.t) (index : Pointer.Index.t) (update : Value.t) :
      option Value.t :=
    match index with
    | Pointer.Index.Tuple index =>
      match value with
      | Tuple fields => Some (Tuple (List.replace_at fields (Z.to_nat index) update))
      | _ => None
      end
    | Pointer.Index.Array index =>
      match value with
      | Array fields =>
        match List.nth_error fields (Z.to_nat index) with
        | Some _ => Some (Array (List.replace_at fields (Z.to_nat index) update))
        | None => None
        end
      | _ => None
      end
    | Pointer.Index.StructRecord constructor field =>
      match value with
      | StructRecord c consts tys fields =>
        match PrimString.compare c constructor with
        | Eq => Some (StructRecord c consts tys (List.assoc_replace fields field update))
        | _ => None
        end
      | _ => None
      end
    | Pointer.Index.StructTuple constructor index =>
      match value with
      | StructTuple c consts tys fields =>
        match PrimString.compare c constructor with
        | Eq => Some (StructTuple c consts tys (List.replace_at fields (Z.to_nat index) update))
        | _ => None
        end
      | _ => None
      end
    end.
End Value.

Module Primitive.
  Inductive t : Set :=
  | StateAlloc
    (ty : Ty.t)
    (value : Value.t)
  | StateRead
    (pointer : Value.t)
  | StateWrite
    (pointer : Value.t)
    (value : Value.t)
  | GetSubPointer
    (pointer : Value.t)
    (index : Pointer.Index.t)
  | GetFunction
    (path : string)
    (generic_consts : list Value.t)
    (generic_tys : list Ty.t)
  | GetAssociatedFunction
    (ty : Ty.t)
    (name : string)
    (generic_consts : list Value.t)
    (generic_tys : list Ty.t)
  | GetTraitMethod
    (trait : string)
    (self_ty : Ty.t)
    (trait_consts : list Value.t)
    (trait_tys : list Ty.t)
    (method : string)
    (generic_consts : list Value.t)
    (generic_tys : list Ty.t).
End Primitive.

Module LogicalOp.
  Inductive t : Set :=
  | And
  | Or.
End LogicalOp.

Module LowM.
  Inductive t (A : Set) : Set :=
  | Pure (value : A)
  | CallPrimitive (primitive : Primitive.t) (k : Value.t -> t A)
  | CallClosure (ty : Ty.t) (closure : Value.t) (args : list Value.t) (k : A -> t A)
  | CallLogicalOp (op : LogicalOp.t) (lhs : Value.t) (rhs : t A) (k : A -> t A)
  | Let (ty : Ty.t) (e : t A) (k : A -> t A)
  | LetAlloc (ty : Ty.t) (e : t A) (k : A -> t A)
  | Loop (ty : Ty.t) (body : t A) (k : A -> t A)
  | MatchTuple (tuple : Value.t) (k : list Value.t -> t A)
  | IfThenElse (ty : Ty.t) (cond : Value.t) (then_ : t A) (else_ : t A) (k : A -> t A)
  | Impossible (message : string).
  Arguments Pure {_}.
  Arguments CallPrimitive {_}.
  Arguments CallClosure {_}.
  Arguments CallLogicalOp {_}.
  Arguments Let {_}.
  Arguments LetAlloc {_}.
  Arguments Loop {_}.
  Arguments MatchTuple {_}.
  Arguments IfThenElse {_}.
  Arguments Impossible {_}.

  Fixpoint let_ {A : Set} (e1 : t A) (e2 : A -> t A) : t A :=
    match e1 with
    | Pure v => e2 v
    | CallPrimitive primitive k =>
      CallPrimitive primitive (fun v => let_ (k v) e2)
    | CallClosure ty f args k =>
      CallClosure ty f args (fun v => let_ (k v) e2)
    | CallLogicalOp op lhs rhs k =>
      CallLogicalOp op lhs rhs (fun v => let_ (k v) e2)
    | Let ty e k =>
      Let ty e (fun v => let_ (k v) e2)
    | Loop ty body k =>
      Loop ty body (fun v => let_ (k v) e2)
    | LetAlloc ty e k =>
      LetAlloc ty e (fun v => let_ (k v) e2)
    | MatchTuple tuple k =>
      MatchTuple tuple (fun fields => let_ (k fields) e2)
    | IfThenElse ty cond then_ else_ k =>
      IfThenElse ty cond then_ else_ (fun v => let_ (k v) e2)
    | Impossible message => Impossible message
    end.
End LowM.

Module Panic.
  Inductive t : Set :=
  | Make (message : string).
End Panic.

Module Exception.
  Inductive t : Set :=
  (** exceptions for Rust's `return` *)
  | Return (value : Value.t) : t
  (** exceptions for Rust's `continue` *)
  | Continue : t
  (** exceptions for Rust's `break` *)
  | Break : t
  (** escape from a match branch once we know that it is not valid *)
  | BreakMatch : t
  | Panic (panic : Panic.t) : t.
End Exception.

Definition M : Set :=
  LowM.t (Value.t + Exception.t).

Definition pure (v : Value.t) : M :=
  LowM.Pure (inl v).
Arguments pure /.

Definition let_ (e1 : M) (e2 : Value.t -> M) : M :=
  LowM.let_ e1 (fun v1 =>
  match v1 with
  | inl v1 => e2 v1
  | inr error => LowM.Pure (inr error)
  end).

Definition let_user (ty : Ty.t) (e1 : Value.t) (e2 : Value.t -> Value.t) : Value.t :=
  e2 e1.

Definition let_user_monadic (ty : Ty.t) (e1 : M) (e2 : Value.t -> M) : M :=
  LowM.LetAlloc ty e1 (fun v1 =>
  match v1 with
  | inl v1 => e2 v1
  | inr error => LowM.Pure (inr error)
  end).
Arguments let_user_monadic /.

Module PolymorphicFunction.
  Definition t : Set :=
    list Value.t -> list Ty.t -> list Value.t -> M.
End PolymorphicFunction.

Module InstanceField.
  Inductive t : Set :=
  | Method (method : PolymorphicFunction.t)
  | Ty (ty : Ty.t).
End InstanceField.

Module Instance.
  Definition t : Set := list (string * InstanceField.t).
End Instance.

Parameter IsTraitInstance :
  forall
    (trait_name : string)
    (trait_consts : list Value.t)
    (trait_tys : list Ty.t)
    (Self : Ty.t)
    (instance : Instance.t),
  Prop.

Module IsFunction.
  Parameter t : forall
    (trait_name : string)
    (function : PolymorphicFunction.t),
    Prop.

  Class C
    (trait_name : string)
    (function : PolymorphicFunction.t) :
    Prop := {
    is_function : t trait_name function;
  }.
End IsFunction.

Module IsAssociatedFunction.
  Parameter t : forall
    (Self : Ty.t)
    (function_name : string)
    (function : PolymorphicFunction.t),
    Prop.

  Class C
    (Self : Ty.t)
    (function_name : string)
    (function : PolymorphicFunction.t) :
    Prop := {
    is_associated_function : t Self function_name function;
  }.
End IsAssociatedFunction.

Parameter IsProvidedMethod :
  forall
    (trait_name : string)
    (method_name : string)
    (method : Ty.t -> PolymorphicFunction.t),
  Prop.

Parameter IsDiscriminant :
  forall
    (variant_name : string)
    (discriminant : Z),
  Prop.

Module IsTraitMethod.
  Inductive t
      (trait_name : string)
      (trait_consts : list Value.t)
      (trait_tys : list Ty.t)
      (self_ty : Ty.t)
      (method_name : string) :
      (PolymorphicFunction.t) -> Prop :=
  | Defined (instance : Instance.t) (method : PolymorphicFunction.t) :
    M.IsTraitInstance
      trait_name
      trait_consts
      trait_tys
      self_ty
      instance ->
    List.assoc instance method_name = Some (InstanceField.Method method) ->
    t trait_name trait_consts trait_tys self_ty method_name method
  | Provided (instance : Instance.t) (method : Ty.t -> PolymorphicFunction.t) :
    M.IsTraitInstance
      trait_name
      trait_consts
      trait_tys
      self_ty
      instance ->
    List.assoc instance method_name = None ->
    M.IsProvidedMethod trait_name method_name method ->
    t trait_name trait_consts trait_tys self_ty method_name (method self_ty).
End IsTraitMethod.

Definition IsTraitAssociatedType
    (trait_name : string)
    (trait_consts : list Value.t)
    (trait_tys : list Ty.t)
    (self_ty : Ty.t)
    (associated_type_name : string)
    (ty : Ty.t) :
    Prop :=
  exists instance,
    M.IsTraitInstance trait_name trait_consts trait_tys self_ty instance /\
    List.assoc instance associated_type_name = Some (InstanceField.Ty ty).

Module Option.
  Definition map {A B : Set} (x : option A) (f : A -> B) : option B :=
    match x with
    | Some x => Some (f x)
    | None => None
    end.

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

  Notation "'let~' a : ty := b 'in' c" :=
    (let_user ty b (fun a => c))
      (at level 200, b at level 100, a name).

  Notation "'let*~' a : ty := b 'in' c" :=
    (let_user_monadic ty b (fun a => c))
      (at level 200, b at level 100, a name).

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
  | context ctxt [let v := ?x in @?f v] =>
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
  (* We uses the `let~` notation for lets that come from the source code, in order to keep this
     abstraction barrier. The code below is simply a copy and paste of the code for the
     normal `let`. *)
  | context ctxt [let~ v : ?ty := ?x in @?f v] =>
    refine (let_user_monadic ty _ _);
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

Definition panic (panic : Panic.t) : M :=
  raise (Exception.Panic panic).

Definition call_closure (ty : Ty.t) (f : Value.t) (args : list Value.t) : M :=
  LowM.CallClosure ty f args LowM.Pure.
Arguments call_closure /.

Definition call_logical_op (op : LogicalOp.t) (lhs : Value.t) (rhs : M) : M :=
  LowM.CallLogicalOp op lhs rhs LowM.Pure.
Arguments call_logical_op /.

Definition impossible (message : string) : M :=
  LowM.Impossible message.

Definition call_primitive (primitive : Primitive.t) : M :=
  LowM.CallPrimitive primitive (fun result =>
  LowM.Pure (inl result)).
(* Make it transparent *)
Arguments call_primitive /.

Definition alloc (ty : Ty.t) (v : Value.t) : M :=
  call_primitive (Primitive.StateAlloc ty v).
Arguments alloc /.

Definition read (pointer : Value.t) : M :=
  call_primitive (Primitive.StateRead pointer).
Arguments read /.

Definition write (pointer : Value.t) (update : Value.t) : M :=
  call_primitive (Primitive.StateWrite pointer update).

Definition copy (ty : Ty.t) (r : Value.t) : M :=
  let* v := read r in
  alloc ty v.
Arguments copy /.

(** If we cannot get the sub-pointer, due to a field that does not exist or to an out-of bound
    access in an array, we do a [break_match]. *)
Definition get_sub_pointer (pointer : Value.t) (index : Pointer.Index.t) : M :=
  call_primitive (Primitive.GetSubPointer pointer index).

Definition get_function (path : string) (generic_consts : list Value.t) (generic_tys : list Ty.t) :
    M :=
  call_primitive (Primitive.GetFunction path generic_consts generic_tys).

Definition get_associated_function
  (ty : Ty.t)
  (name : string)
  (generic_consts : list Value.t)
  (generic_tys : list Ty.t) :
  M :=
  call_primitive (Primitive.GetAssociatedFunction ty name generic_consts generic_tys).

Definition get_trait_method
    (trait : string)
    (self_ty : Ty.t)
    (trait_consts : list Value.t)
    (trait_tys : list Ty.t)
    (method : string)
    (generic_consts : list Value.t)
    (generic_tys : list Ty.t) :
    M :=
  call_primitive (Primitive.GetTraitMethod
    trait self_ty trait_consts trait_tys method generic_consts generic_tys
  ).

Definition catch (ty : Ty.t) (body : M) (handler : Exception.t -> M) : M :=
  LowM.Let ty body (fun result =>
  match result with
  | inl v => pure v
  | inr exception => handler exception
  end).

Definition catch_return (ty : Ty.t) (body : M) : M :=
  catch
    ty
    body
    (fun exception =>
      match exception with
      | Exception.Return r => pure r
      | _ => raise exception
      end
    ).

Definition catch_continue (ty : Ty.t) (body : M) : M :=
  catch
    ty
    body
    (fun exception =>
      match exception with
      | Exception.Continue => alloc (Ty.tuple []) (Value.Tuple [])
      | _ => raise exception
      end
    ).

Definition catch_break (ty : Ty.t) (body : M) : M :=
  catch
    ty
    body
    (fun exception =>
      match exception with
      | Exception.Break => alloc (Ty.tuple []) (Value.Tuple [])
      | _ => raise exception
      end
    ).

Definition loop (ty : Ty.t) (body : M) : M :=
  LowM.Loop
    ty
    (let_ (catch_continue ty body) read)
    (fun result =>
      catch_break ty (LowM.Pure result)).

(** The type [ty] is the type of each arm. *)
Fixpoint match_operator
    (ty : Ty.t)
    (scrutinee : Value.t)
    (arms : list (Value.t -> M)) :
    M :=
  match arms with
  | nil =>
    (* It should ideally be an [impossible] case, but that would make the links more complex *)
    panic (Panic.Make "no match branches left")
  | arm :: arms =>
    catch
      ty
      (arm scrutinee)
      (fun exception =>
        match exception with
        | Exception.BreakMatch => match_operator ty scrutinee arms
        | _ => raise exception
        end
      )
  end.

(** Each arm must return a tuple of the free variables found in the pattern. If
    no arms are valid, we raise an [Exception.BreakMatch].
*)
Fixpoint find_or_pattern_aux
    (arm_ty : Ty.t)
    (scrutinee : Value.t)
    (arms : list (Value.t -> M)) :
    M :=
  match arms with
  | nil => break_match
  | arm :: arms =>
    catch
      arm_ty
      (arm scrutinee)
      (fun exception =>
        match exception with
        | Exception.BreakMatch => find_or_pattern_aux arm_ty scrutinee arms
        | _ => raise exception
        end
      )
  end.

Definition find_or_pattern
    (arm_ty : Ty.t)
    (scrutinee : Value.t)
    (arms : list (Value.t -> M))
    (body : list Value.t -> M) :
    M :=
  let* free_vars := find_or_pattern_aux arm_ty scrutinee arms in
  LowM.MatchTuple free_vars body.

Definition never_to_any (x : Value.t) : M :=
  M.panic (Panic.Make "never_to_any got called").

Definition use (x : Value.t) : Value.t :=
  x.

Definition borrow (kind : Pointer.Kind.t) (value : Value.t) : M :=
  match value with
  | Value.Pointer {| Pointer.kind := Pointer.Kind.Raw; Pointer.core := core |} =>
    pure (Value.Pointer {| Pointer.kind := kind; Pointer.core := core |})
  | _ => impossible "expected a raw pointer"
  end.
Global Opaque borrow.

Definition deref (value : Value.t) : M :=
  match value with
  | Value.Pointer pointer => pure (Value.Pointer (Pointer.deref pointer))
  | _ => impossible "expected a pointer"
  end.
Global Opaque deref.

Module SubPointer.
  Definition get_tuple_field (value : Value.t) (index : Z) : M :=
    get_sub_pointer value (Pointer.Index.Tuple index).

  Definition get_array_field (value : Value.t) (index : Value.t) : M :=
    match index with
    | Value.Integer IntegerKind.Usize index => get_sub_pointer value (Pointer.Index.Array index)
    | _ => impossible "expected a usize integer as an array index"
    end.

  Definition get_struct_tuple_field (value : Value.t) (constructor : string) (index : Z) : M :=
    let* value := deref value in
    get_sub_pointer value (Pointer.Index.StructTuple constructor index).
  Arguments get_struct_tuple_field /.

  Definition get_struct_record_field (value : Value.t) (constructor field : string) : M :=
    get_sub_pointer value (Pointer.Index.StructRecord constructor field).

  (** Get an element of a slice by index. *)
  Definition get_slice_index (value : Value.t) (index : Z) : M :=
    get_sub_pointer value (Pointer.Index.Array index).

  (** Get an element of a slice by index counting from the end. *)
  Parameter get_slice_rev_index : Value.t -> Z -> M.

  (** For two indices n and k, get all elements of a slice without
      the first n elements and without the last k elements. *)
  Parameter get_slice_rest : Value.t -> Z -> Z -> M.
End SubPointer.

Definition if_then_else_bool (ty : Ty.t) (condition : Value.t) (then_ else_ : M) : M :=
  LowM.IfThenElse ty condition then_ else_ LowM.Pure.

Definition is_struct_tuple (value : Value.t) (constructor : string) : M :=
  let* value := deref value in
  let* value := read value in
  match value with
  | Value.StructTuple current_constructor _ _ _ =>
    match PrimString.compare current_constructor constructor with
    | Eq => pure (Value.Tuple [])
    | _ => break_match
    end
  | _ => break_match
  end.
Arguments is_struct_tuple /.

(*
  pub enum PointerCoercion {
      ReifyFnPointer,
      UnsafeFnPointer,
      ClosureFnPointer(Safety),
      MutToConstPointer,
      ArrayToPointer,
      Unsize,
      DynStar,
  }
*)
Module PointerCoercion.
  (*
    pub enum Safety {
        Unsafe,
        Safe,
    }
  *)
  Module Safety.
    Inductive t : Set :=
    | Unsafe
    | Safe.
  End Safety.

  Inductive t : Set :=
  | ReifyFnPointer
  | UnsafeFnPointer
  | ClosureFnPointer (safety : Safety.t)
  | MutToConstPointer
  | ArrayToPointer
  | Unsize
  | DynStar.
End PointerCoercion.

(** This function is explicitly called in the Rust AST, and should take two
    types that are actually different but convertible, like different kinds of
    integers. *)
Parameter cast : Ty.t -> Value.t -> Value.t.

Definition closure (f : list Value.t -> M) : Value.t :=
  Value.Closure (existS (_, _) f).

Definition constructor_as_closure (constructor : string) (consts : list Value.t) (tys : list Ty.t) :
    Value.t :=
  closure (fun args =>
    pure (Value.StructTuple constructor consts tys args)).

Parameter pointer_coercion_intrinsic : PointerCoercion.t -> PolymorphicFunction.t.

Definition pointer_coercion (coercion : PointerCoercion.t) (source target : Ty.t) : Value.t :=
  M.closure (pointer_coercion_intrinsic coercion [] [source; target]).
Arguments pointer_coercion /.

Parameter struct_record_update : Value.t -> list (string * Value.t) -> Value.t.

Parameter unevaluated_const : Value.t -> Value.t.

Parameter yield : Value.t -> M.
