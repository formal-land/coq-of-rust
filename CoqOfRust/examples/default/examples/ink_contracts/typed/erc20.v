Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.typed.M.
Require Import CoqOfRust.lib.typed.lib.
Require CoqOfRust.examples.default.examples.ink_contracts.erc20.

Import M.Notations.
Import Run.

Module Mapping.
  Parameter t : Set -> Set -> Set.

  Parameter to_value : forall {K V : Set} `{ToValue K} `{ToValue V}, t K V -> Value.t.

  Global Instance IsToValue (K V : Set) `{ToValue K} `{ToValue V} : ToValue (t K V) := {
    Φ := Ty.apply (Ty.path "erc20::Mapping") [Φ K; Φ V];
    φ := to_value;
  }.
End Mapping.

Module Impl_erc20_Mapping_K_V.
  Parameter get : forall {K V : Set} `{ToValue K} `{ToValue V},
    Pointer.t (Mapping.t K V) -> Pointer.t K -> M (option V).

  Parameter insert : forall {K V : Set} `{ToValue K} `{ToValue V},
    Pointer.t (Mapping.t K V) -> K -> V -> M unit.
End Impl_erc20_Mapping_K_V.

Module Balance.
  Definition t : Set := u128.t.
End Balance.

Module AccountId.
  Inductive t : Set :=
  | Make (account_id : u128.t).

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc20::AccountId";
    φ '(Make x) := Value.StructTuple "erc20::AccountId" [φ x];
  }.
End AccountId.

(* TODO: move to the right place *)
Module Pointer.
  Global Instance IsToValue {T : Set} `{ToValue T} : ToValue (Pointer.t T) := {
    Φ := Ty.path "erc20::Pointer"; (* TODO *)
    φ x := Value.Pointer (Pointer.to_pointer x);
  }.
End Pointer.

Module Erc20.
  Record t : Set := {
    total_supply : Balance.t;
    balances : Mapping.t AccountId.t Balance.t;
    allowances : Mapping.t (AccountId.t * AccountId.t) Balance.t;
  }.

  Global Instance IsToValue : ToValue t := {
    Φ := Ty.path "erc20::Erc20";
    φ x :=
      Value.StructRecord "erc20::Erc20" [
        ("total_supply", φ x.(total_supply));
        ("balances", φ x.(balances));
        ("allowances", φ x.(allowances))
      ];
  }.

  Definition get_total_supply (self : Pointer.t t) : M (Pointer.t Balance.t) :=
    M.make_sub_pointer self (Pointer.Index.StructRecord "erc20::Erc20" "total_supply")
      (fun x => Some x.(total_supply))
      (fun x v => Some (x <| total_supply := v |>)).

  Lemma get_total_supply_run {Address Env : Set} (env_to_value : Env -> Value.t)
      (self : Pointer.t t) :
    {{ Address, env_to_value |
      get_struct_record_field_closure "erc20::Erc20" "total_supply" [φ self] ~
      Erc20.get_total_supply self
    }}.
  Proof.
    destruct self, origin.
    apply Run.CallPrimitiveMakeSubPointer; try reflexivity.
    apply Run.Pure.
    reflexivity.
  Qed.
End Erc20.

Module Impl_erc20_Erc20.
  Definition Self : Set := Erc20.t.

  Definition total_supply (self : Pointer.t Self) : M Balance.t :=
    let* self := M.alloc self in
    let* self := M.read self in
    let* self_total_supply := M.call_closure Erc20.get_total_supply <[self]> in
    M.read self_total_supply.

  Lemma total_supply_run {Address Env : Set} (env_to_value : Env -> Value.t)
      (self : Pointer.t Self) :
    {{ Address, env_to_value |
      ink_contracts.erc20.Impl_erc20_Erc20.total_supply [] [φ self] ~
      total_supply self
    }}.
  Proof.
    Opaque φ.
    cbn.
    apply Run.CallPrimitiveStateAlloc.
    intros; cbn.
    apply Run.CallPrimitiveStateRead; [reflexivity|].
    intros.
    eapply Run.CallClosure; try constructor. {
      apply Erc20.get_total_supply_run.
    }
    intros.
    destruct result as [|[[] | | | | ]]; cbn; try now apply Run.Pure.
    destruct t0.
    apply Run.CallPrimitiveStateRead; [reflexivity|]; intros.
    now apply Run.Pure.
  Qed.

  (* Definition balance_of_impl (self : Pointer.t Erc20.t) (owner : Pointer.t AccountId) :
      M (option Balance.t) :=
    let* self := M.read self in *)

    Impl_erc20_Mapping_K_V.get mapping owner.
End Impl_erc20_Erc20.
