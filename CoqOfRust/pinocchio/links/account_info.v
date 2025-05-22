Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import pinocchio.links.pubkey.
Require Import pinocchio.account_info.

Module Account.
    Record t : Set := {
        borrow_state : U8.t;
        is_signer: U8.t;
        is_writable: U8.t;
        executable: U8.t;
        key: Pubkey.t;
        owner: Pubkey.t;
        lamports: U64.t;
        data_len: U64.t
    }.

    Global Instance IsLink : Link t := {
        Φ := Ty.path "pinocchio::account_info::Account";
        φ x :=
      Value.StructRecord "pinocchio::account_info::Account" [] [] [
        ("borrow_state", φ x.(borrow_state));
        ("is_signer", φ x.(is_signer));
        ("is_writable", φ x.(is_writable));
        ("executable", φ x.(executable));
        ("key", φ x.(key));
        ("owner", φ x.(owner));
        ("lamports", φ x.(lamports));
        ("data_len", φ x.(data_len))
      ];
    }.

    Definition of_ty : OfTy.t (Ty.path "pinocchio::account_info::Account").
    Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
    Smpl Add apply of_ty : of_ty.

    Lemma of_value_with
    (borrow_state : U8.t) (borrow_state' : Value.t)
    (is_signer : U8.t) (is_signer' : Value.t)
    (is_writable : U8.t) (is_writable' : Value.t)
    (executable : U8.t) (executable' : Value.t)
    (key : Pubkey.t) (key' : Value.t)
    (owner : Pubkey.t) (owner' : Value.t)
    (lamports : U64.t) (lamports' : Value.t)
    (data_len : U64.t) (data_len' : Value.t)
    :
    borrow_state' = φ borrow_state ->
    is_signer' = φ is_signer ->
    is_writable' = φ is_writable ->
    executable' = φ executable ->
    key' = φ key ->
    owner' = φ owner ->
    lamports' = φ lamports ->
    data_len' = φ data_len ->
    Value.StructRecord "pinocchio::account_info::Account" [] [] [
      ("borrow_state", borrow_state');
      ("is_signer", is_signer');
      ("is_writable", is_writable');
      ("executable", executable');
      ("key", key');
      ("owner", owner');
      ("lamports", lamports');
      ("data_len", data_len')
    ] = φ (Build_t borrow_state is_signer is_writable executable key owner lamports data_len).
  Proof. intros; subst; reflexivity. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value
    (borrow_state : U8.t) (borrow_state' : Value.t)
    (is_signer : U8.t) (is_signer' : Value.t)
    (is_writable : U8.t) (is_writable' : Value.t)
    (executable : U8.t) (executable' : Value.t)
    (key : Pubkey.t) (key' : Value.t)
    (owner : Pubkey.t) (owner' : Value.t)
    (lamports : U64.t) (lamports' : Value.t)
    (data_len : U64.t) (data_len' : Value.t):
    borrow_state' = φ borrow_state ->
    is_signer' = φ is_signer ->
    is_writable' = φ is_writable ->
    executable' = φ executable ->
    key' = φ key ->
    owner' = φ owner ->
    lamports' = φ lamports ->
    data_len' = φ data_len ->
    OfValue.t (
      Value.StructRecord "pinocchio::account_info::Account" [] [] [
        ("borrow_state", borrow_state');
        ("is_signer", is_signer');
        ("is_writable", is_writable');
        ("executable", executable');
        ("key", key');
        ("owner", owner');
        ("lamports", lamports');
        ("data_len", data_len')
      ]).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add apply of_value : of_value.
End Account.