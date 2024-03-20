Require Import CoqOfRust.CoqOfRust.

(** A purely functional map data structure, used later to implement the mapping
    data structure of ink!. *)
Module Mapping.
  (** t K V *)
  Parameter empty : Value.t.

  (** K -> t K V -> option V *)
  Parameter get : Value.t -> Value.t -> Value.t.

  (** K -> V -> t K V -> t K V *)
  Parameter insert : Value.t -> Value.t -> Value.t -> Value.t.

  (** (V -> Z) -> t K V -> Z *)
  Parameter sum : (Value.t -> Z) -> Value.t -> Z.
End Mapping.

Module Impl_Mapping_t_K_V.
  Definition Self (K V : Ty.t) : Ty.t :=
    Ty.apply (Ty.path "erc20::Mapping") [ K; V ].
  
  (** fn get(&self, key: &K) -> Option<V> *)
  Definition get (K V : Ty.t) (𝜏 : list Ty.t) (α : list Value.t) : M :=
    let Self : Ty.t := Self K V in
    match 𝜏, α with
    | [], [ self; key ] =>
      let* self := M.read self in
      let* key := M.read key in
      M.pure (Mapping.get key self)
    | _, _ => M.impossible
    end.
  
  Axiom AssociatedFunction_get :
    forall (K V : Ty.t),
    M.IsAssociatedFunction (Self K V) "get" (get K V).
  
  (** fn insert(&mut self, key: K, value: V) *)
  Definition insert
    (K V : Ty.t) (𝜏 : list Ty.t) (α : list Value.t) : M :=
    let Self : Ty.t := Self K V in
    match 𝜏, α with
    | [], [ self; key; value ] =>
      let* self_content := M.read self in
      let new_self_content := Mapping.insert key value self_content in
      let* _ := assign self new_self_content in
      M.pure (Value.Tuple [])
    | _, _ => M.impossible
    end.
  
  Axiom AssociatedFunction_insert :
    forall (K V : Ty.t),
    M.IsAssociatedFunction (Self K V) "insert" (get K V).
End Impl_Mapping_t_K_V.
