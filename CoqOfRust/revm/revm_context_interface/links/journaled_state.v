Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.option.
Require Import core.ops.links.deref.
Require Import revm.revm_context_interface.journaled_state.

(*
pub struct StateLoad<T> {
    pub data: T,
    pub is_cold: bool,
}
*)
Module StateLoad.
  Record t {T : Set} : Set := {
    data : T;
    is_cold : bool;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink {T : Set} `{Link T} : Link (t T) := {
    Φ := Ty.apply (Ty.path "revm_context_interface::journaled_state::StateLoad") [] [Φ T];
    φ x :=
      Value.StructRecord "revm_context_interface::journaled_state::StateLoad" [] [] [
        ("data", φ x.(data));
        ("is_cold", φ x.(is_cold))
      ];
  }.

  Definition of_ty (T_ty : Ty.t) :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "revm_context_interface::journaled_state::StateLoad") [] [T_ty]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    now subst.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with (T : Set) `{Link T}
      (data : T) data'
      (is_cold : bool) is_cold' :
    data' = φ data ->
    is_cold' = φ is_cold ->
    Value.StructRecord "revm_context_interface::journaled_state::StateLoad" [] [] [
      ("data", data');
      ("is_cold", is_cold')
    ] = φ (Build_t _ data is_cold).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add eapply of_value_with : of_value.

  Module SubPointer.
    Definition get_data (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::StateLoad" "data") :=
    {|
      SubPointer.Runner.projection x := Some x.(data);
      SubPointer.Runner.injection x y := Some (x <| data := y |>);
    |}.

    Lemma get_data_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_data T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_data_is_valid : run_sub_pointer.

    Definition get_is_cold (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::StateLoad" "is_cold") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_cold);
      SubPointer.Runner.injection x y := Some (x <| is_cold := y |>);
    |}.

    Lemma get_is_cold_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_is_cold T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_is_cold_is_valid : run_sub_pointer.
  End SubPointer.
End StateLoad.

(*
impl<T> Deref for StateLoad<T> {
    type Target = T;
*)
Module Impl_Deref_for_StateLoad.
  Definition Self (T : Set) : Set :=
    StateLoad.t T.

  Instance run (T : Set) `{Link T} : Deref.Run (Self T) T.
  Admitted.
End Impl_Deref_for_StateLoad.
Export Impl_Deref_for_StateLoad.

(*
pub struct Eip7702CodeLoad<T> {
    pub state_load: StateLoad<T>,
    pub is_delegate_account_cold: Option<bool>,
}
*)
Module Eip7702CodeLoad.
  Record t {T : Set} : Set := {
    state_load : StateLoad.t T;
    is_delegate_account_cold : option bool;
  }.
  Arguments t : clear implicits.

  Global Instance IsLink {T : Set} `{Link T} : Link (t T) :=
  {
    Φ := Ty.apply (Ty.path "revm_context_interface::journaled_state::Eip7702CodeLoad") [] [Φ T];
    φ x :=
      Value.StructRecord "revm_context_interface::journaled_state::Eip7702CodeLoad" [] [] [
        ("state_load", φ x.(state_load));
        ("is_delegate_account_cold", φ x.(is_delegate_account_cold))
      ];
  }.

  Definition of_ty (T_ty : Ty.t) :
    OfTy.t T_ty ->
    OfTy.t (Ty.apply (Ty.path "revm_context_interface::journaled_state::Eip7702CodeLoad") [] [T_ty]).
  Proof.
    intros [T].
    eapply OfTy.Make with (A := t T).
    now subst.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with state_load state_load' is_delegate_account_cold is_delegate_account_cold' :
    state_load' = φ state_load ->
    is_delegate_account_cold' = φ is_delegate_account_cold ->
    Value.StructRecord "revm_context_interface::journaled_state::Eip7702CodeLoad" [] [] [
      ("state_load", state_load');
      ("is_delegate_account_cold", is_delegate_account_cold')
    ] = φ (Build_t _ state_load is_delegate_account_cold).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add apply of_value_with : of_value.

  Module SubPointer.
    Definition get_state_load (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::Eip7702CodeLoad" "state_load") :=
    {|
      SubPointer.Runner.projection x := Some x.(state_load);
      SubPointer.Runner.injection x y := Some (x <| state_load := y |>);
    |}.

    Lemma get_state_load_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_state_load T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_state_load_is_valid : run_sub_pointer.

    Definition get_is_delegate_account_cold (T : Set) `{Link T} : SubPointer.Runner.t (t T)
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::Eip7702CodeLoad" "is_delegate_account_cold") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_delegate_account_cold);
      SubPointer.Runner.injection x y := Some (x <| is_delegate_account_cold := y |>);
    |}.

    Lemma get_is_delegate_account_cold_is_valid (T : Set) `{Link T} :
      SubPointer.Runner.Valid.t (get_is_delegate_account_cold T).
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_is_delegate_account_cold_is_valid : run_sub_pointer.
  End SubPointer.
End Eip7702CodeLoad.

Module Impl_Eip7702CodeLoad.
  Definition Self (T : Set) `{Link T} : Set :=
    Eip7702CodeLoad.t T.

  (* pub fn into_components(self) -> (T, Eip7702CodeLoad<()>) *)
  Instance run_into_components (T : Set) `{Link T} (self : Self T) :
    Run.Trait
      (journaled_state.Impl_revm_context_interface_journaled_state_Eip7702CodeLoad_T.into_components (Φ T))
      [] [] [ φ self ] (T * Self unit).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_Eip7702CodeLoad.
Export Impl_Eip7702CodeLoad.

(*
pub struct AccountLoad {
    pub load: Eip7702CodeLoad<()>,
    pub is_empty: bool,
}
*)
Module AccountLoad.
  Record t : Set := {
    load : Eip7702CodeLoad.t unit;
    is_empty : bool;
  }.

  Global Instance IsLink : Link t :=
  {
    Φ := Ty.path "revm_context_interface::journaled_state::AccountLoad";
    φ x :=
      Value.StructRecord "revm_context_interface::journaled_state::AccountLoad" [] [] [
        ("load", φ x.(load));
        ("is_empty", φ x.(is_empty))
      ];
  }.
  
  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::journaled_state::AccountLoad").
  Proof.
    eapply OfTy.Make with (A := t).
    reflexivity.
  Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with load load' is_empty is_empty' :
    load' = φ load ->
    is_empty' = φ is_empty ->
    Value.StructRecord "revm_context_interface::journaled_state::AccountLoad" [] [] [
      ("load", load');
      ("is_empty", is_empty')
    ] = φ (Build_t load is_empty).
  Proof.
    now intros; subst.
  Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (load : Eip7702CodeLoad.t unit) load' (is_empty : bool) is_empty' :
    load' = φ load ->
    is_empty' = φ is_empty ->
    OfValue.t (
      Value.StructRecord "revm_context_interface::journaled_state::AccountLoad" [] [] [
        ("load", load');
        ("is_empty", is_empty')
      ]
    ).
  Proof.
    econstructor; apply of_value_with; eassumption.
  Defined.
  Smpl Add apply of_value : of_value.

  Module SubPointer.
    Definition get_load : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::AccountLoad" "load") :=
    {|
      SubPointer.Runner.projection x := Some x.(load);
      SubPointer.Runner.injection x y := Some (x <| load := y |>);
    |}.

    Lemma get_load_is_valid :
      SubPointer.Runner.Valid.t get_load.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_load_is_valid : run_sub_pointer.

    Definition get_is_empty : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_context_interface::journaled_state::AccountLoad" "is_empty") :=
    {|
      SubPointer.Runner.projection x := Some x.(is_empty);
      SubPointer.Runner.injection x y := Some (x <| is_empty := y |>);
    |}.

    Lemma get_is_empty_is_valid :
      SubPointer.Runner.Valid.t get_is_empty.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_is_empty_is_valid : run_sub_pointer.
  End SubPointer.
End AccountLoad.
