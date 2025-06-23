Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import pinocchio.links.pubkey.
Require Import pinocchio.account_info.

Import account_info.Impl_pinocchio_account_info_AccountInfo.

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

  Module SubPointer.
    Definition get_borrow_state : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "pinocchio::account_info::Account" "borrow_state") :=
      {|
        SubPointer.Runner.projection x := Some x.(borrow_state);
        SubPointer.Runner.injection x y := Some (x <| borrow_state := y |>);
      |}.

    Lemma get_borrow_state_is_valid :
      SubPointer.Runner.Valid.t get_borrow_state.
    Proof. now constructor. Qed.
    Smpl Add apply get_borrow_state_is_valid : run_sub_pointer.

    Definition get_is_signer : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "pinocchio::account_info::Account" "is_signer") :=
      {|
        SubPointer.Runner.projection x := Some x.(is_signer);
        SubPointer.Runner.injection x y := Some (x <| is_signer := y |>);
      |}.

    Lemma get_is_signer_is_valid :
      SubPointer.Runner.Valid.t get_is_signer.
    Proof. now constructor. Qed.
    Smpl Add apply get_is_signer_is_valid : run_sub_pointer.

    Definition get_is_writable : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "pinocchio::account_info::Account" "is_writable") :=
      {|
        SubPointer.Runner.projection x := Some x.(is_writable);
        SubPointer.Runner.injection x y := Some (x <| is_writable := y |>);
      |}.

    Lemma get_is_writable_is_valid :
      SubPointer.Runner.Valid.t get_is_writable.
    Proof. now constructor. Qed.
    Smpl Add apply get_is_writable_is_valid : run_sub_pointer.

    Definition get_executable : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "pinocchio::account_info::Account" "executable") :=
      {|
        SubPointer.Runner.projection x := Some x.(executable);
        SubPointer.Runner.injection x y := Some (x <| executable := y |>);
      |}.

    Lemma get_executable_is_valid :
      SubPointer.Runner.Valid.t get_executable.
    Proof. now constructor. Qed.
    Smpl Add apply get_executable_is_valid : run_sub_pointer.

    Definition get_key : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "pinocchio::account_info::Account" "key") :=
      {|
        SubPointer.Runner.projection x := Some x.(key);
        SubPointer.Runner.injection x y := Some (x <| key := y |>);
      |}.

    Lemma get_key_is_valid :
      SubPointer.Runner.Valid.t get_key.
    Proof. now constructor. Qed.
    Smpl Add apply get_key_is_valid : run_sub_pointer.

    Definition get_owner : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "pinocchio::account_info::Account" "owner") :=
      {|
        SubPointer.Runner.projection x := Some x.(owner);
        SubPointer.Runner.injection x y := Some (x <| owner := y |>);
      |}.

    Lemma get_owner_is_valid :
      SubPointer.Runner.Valid.t get_owner.
    Proof. now constructor. Qed.
    Smpl Add apply get_owner_is_valid : run_sub_pointer.

    Definition get_lamports : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "pinocchio::account_info::Account" "lamports") :=
      {|
        SubPointer.Runner.projection x := Some x.(lamports);
        SubPointer.Runner.injection x y := Some (x <| lamports := y |>);
      |}.

    Lemma get_lamports_is_valid :
      SubPointer.Runner.Valid.t get_lamports.
    Proof. now constructor. Qed.
    Smpl Add apply get_lamports_is_valid : run_sub_pointer.

    Definition get_data_len : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "pinocchio::account_info::Account" "data_len") :=
      {|
        SubPointer.Runner.projection x := Some x.(data_len);
        SubPointer.Runner.injection x y := Some (x <| data_len := y |>);
      |}.

    Lemma get_data_len_is_valid :
      SubPointer.Runner.Valid.t get_data_len.
    Proof. now constructor. Qed.
    Smpl Add apply get_data_len_is_valid : run_sub_pointer.

  End SubPointer.
End Account.

Module AccountInfo.
    Record t : Set := {
      raw : Ref.t Pointer.Kind.Ref Account.t;
    }.
  
    Global Instance IsLink : Link t := {
      Φ := Ty.path "pinocchio::account_info::AccountInfo";
      φ x :=
        Value.StructRecord "pinocchio::account_info::AccountInfo" [] [] [
          ("raw", φ x.(raw))
        ];
    }.
  
    Definition of_ty : OfTy.t (Ty.path "pinocchio::account_info::AccountInfo").
    Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
    Smpl Add apply of_ty : of_ty.
  
    Lemma of_value_with (raw : Ref.t Pointer.Kind.Ref Account.t) (raw' : Value.t) :
      raw' = φ raw ->
      Value.StructRecord "pinocchio::account_info::AccountInfo" [] [] [
        ("raw", raw')
      ] = φ (Build_t raw).
    Proof. intros; subst; reflexivity. Qed.
    Smpl Add apply of_value_with : of_value.
  
    Definition of_value (raw : Ref.t Pointer.Kind.Ref Account.t) (raw' : Value.t) :
      raw' = φ raw ->
      OfValue.t (
        Value.StructRecord "pinocchio::account_info::AccountInfo" [] [] [
          ("raw", raw')
        ]).
    Proof. econstructor; apply of_value_with. exact H. Defined.
    Smpl Add apply of_value : of_value.

    Module SubPointer.
      Definition get_raw : SubPointer.Runner.t t
        (Pointer.Index.StructRecord "pinocchio::account_info::AccountInfo" "raw") :=
      {|
        SubPointer.Runner.projection x := Some x.(raw);
        SubPointer.Runner.injection x y := Some (x <| raw := y |>);
      |}.
  
      Lemma get_raw_is_valid :
        SubPointer.Runner.Valid.t get_raw.
      Proof. now constructor. Qed.
      Smpl Add apply get_raw_is_valid : run_sub_pointer.
    End SubPointer.
  End AccountInfo.

  Module Impl_AccountInfo.
    Definition Self : Set := AccountInfo.t.
    Instance run_key 
        (self : Ref.t Pointer.Kind.MutRef Self) :
      Run.Trait
        key [] [] [φ self]
        (Ref.t Pointer.Kind.MutRef Pubkey.t).
    Proof.
      constructor.
      run_symbolic.
      - admit.
      - admit.
    Admitted.
  End Impl_AccountInfo.
  