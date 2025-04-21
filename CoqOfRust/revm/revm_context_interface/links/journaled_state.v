Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import CoqOfRust.revm.revm_context_interface.journaled_state.

(*
pub struct Eip7702CodeLoad<T> {
    pub state_load: StateLoad<T>,
    pub is_delegate_account_cold: Option<bool>,
}
*)
Module Eip7702CodeLoad.
  Parameter t : forall (T : Set), Set.

  Global Instance IsLink {T : Set} `{Link T} : Link (t T).
  Admitted.
End Eip7702CodeLoad.

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
      Value.StructRecord "revm_context_interface::journaled_state::AccountLoad" [
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
    Value.StructRecord "revm_context_interface::journaled_state::AccountLoad" [
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
      Value.StructRecord "revm_context_interface::journaled_state::AccountLoad" [
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

(*
pub struct StateLoad<T> {
    pub data: T,
    pub is_cold: bool,
}
*)
Module StateLoad.
  Parameter t : forall (T : Set), Set.

  Global Instance IsLink {T : Set} `{Link T} : Link (t T).
  Admitted.
End StateLoad.
