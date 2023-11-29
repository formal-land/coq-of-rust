(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Module  Account.
Section Account.
  Record t : Set := {
    username : ref str.t;
    password : ref str.t;
  }.
  
  Global Instance Get_username : Notations.Dot "username" := {
    Notations.dot :=
      Ref.map (fun x => x.(username)) (fun v x => x <| username := v |>);
  }.
  Global Instance Get_AF_username : Notations.DoubleColon t "username" := {
    Notations.double_colon (x : M.Val t) := x.["username"];
  }.
  Global Instance Get_password : Notations.Dot "password" := {
    Notations.dot :=
      Ref.map (fun x => x.(password)) (fun v x => x <| password := v |>);
  }.
  Global Instance Get_AF_password : Notations.DoubleColon t "password" := {
    Notations.double_colon (x : M.Val t) := x.["password"];
  }.
End Account.
End Account.

Module  Impl_core_marker_StructuralPartialEq_for_hash_map_alternate_or_custom_key_types_Account_t.
Section Impl_core_marker_StructuralPartialEq_for_hash_map_alternate_or_custom_key_types_Account_t.
  Ltac Self := exact hash_map_alternate_or_custom_key_types.Account.t.
  
  Global Instance ℐ : core.marker.StructuralPartialEq.Trait ltac:(Self) := {
  }.
End Impl_core_marker_StructuralPartialEq_for_hash_map_alternate_or_custom_key_types_Account_t.
End Impl_core_marker_StructuralPartialEq_for_hash_map_alternate_or_custom_key_types_Account_t.

Module  Impl_core_cmp_PartialEq_for_hash_map_alternate_or_custom_key_types_Account_t.
Section Impl_core_cmp_PartialEq_for_hash_map_alternate_or_custom_key_types_Account_t.
  Ltac Self := exact hash_map_alternate_or_custom_key_types.Account.t.
  
  (*
  PartialEq
  *)
  Parameter eq :
      (ref ltac:(Self)) ->
        (ref hash_map_alternate_or_custom_key_types.Account.t) ->
        M bool.t.
  
  Global Instance AssociatedFunction_eq :
    Notations.DoubleColon ltac:(Self) "eq" := {
    Notations.double_colon := eq;
  }.
  
  Global Instance ℐ :
    core.cmp.PartialEq.Required.Trait ltac:(Self)
      (Rhs := core.cmp.PartialEq.Default.Rhs ltac:(Self)) := {
    core.cmp.PartialEq.eq := eq;
    core.cmp.PartialEq.ne := Datatypes.None;
  }.
End Impl_core_cmp_PartialEq_for_hash_map_alternate_or_custom_key_types_Account_t.
End Impl_core_cmp_PartialEq_for_hash_map_alternate_or_custom_key_types_Account_t.

Module  Impl_core_marker_StructuralEq_for_hash_map_alternate_or_custom_key_types_Account_t.
Section Impl_core_marker_StructuralEq_for_hash_map_alternate_or_custom_key_types_Account_t.
  Ltac Self := exact hash_map_alternate_or_custom_key_types.Account.t.
  
  Global Instance ℐ : core.marker.StructuralEq.Trait ltac:(Self) := {
  }.
End Impl_core_marker_StructuralEq_for_hash_map_alternate_or_custom_key_types_Account_t.
End Impl_core_marker_StructuralEq_for_hash_map_alternate_or_custom_key_types_Account_t.

Module  Impl_core_cmp_Eq_for_hash_map_alternate_or_custom_key_types_Account_t.
Section Impl_core_cmp_Eq_for_hash_map_alternate_or_custom_key_types_Account_t.
  Ltac Self := exact hash_map_alternate_or_custom_key_types.Account.t.
  
  (*
  Eq
  *)
  Parameter assert_receiver_is_total_eq : (ref ltac:(Self)) -> M unit.
  
  Global Instance AssociatedFunction_assert_receiver_is_total_eq :
    Notations.DoubleColon ltac:(Self) "assert_receiver_is_total_eq" := {
    Notations.double_colon := assert_receiver_is_total_eq;
  }.
  
  Global Instance ℐ : core.cmp.Eq.Required.Trait ltac:(Self) := {
    core.cmp.Eq.assert_receiver_is_total_eq :=
      Datatypes.Some assert_receiver_is_total_eq;
  }.
End Impl_core_cmp_Eq_for_hash_map_alternate_or_custom_key_types_Account_t.
End Impl_core_cmp_Eq_for_hash_map_alternate_or_custom_key_types_Account_t.

Module  Impl_core_hash_Hash_for_hash_map_alternate_or_custom_key_types_Account_t.
Section Impl_core_hash_Hash_for_hash_map_alternate_or_custom_key_types_Account_t.
  Ltac Self := exact hash_map_alternate_or_custom_key_types.Account.t.
  
  (*
  Hash
  *)
  Parameter hash :
      forall {__H : Set} {ℋ_0 : core.hash.Hasher.Trait __H},
      (ref ltac:(Self)) -> (mut_ref __H) -> M unit.
  
  Global Instance AssociatedFunction_hash
      {__H : Set}
      {ℋ_0 : core.hash.Hasher.Trait __H} :
    Notations.DoubleColon ltac:(Self) "hash" := {
    Notations.double_colon := hash (__H := __H);
  }.
  
  Global Instance ℐ : core.hash.Hash.Required.Trait ltac:(Self) := {
    core.hash.Hash.hash {__H : Set} {ℋ_0 : core.hash.Hasher.Trait __H} :=
      hash (__H := __H);
    core.hash.Hash.hash_slice := Datatypes.None;
  }.
End Impl_core_hash_Hash_for_hash_map_alternate_or_custom_key_types_Account_t.
End Impl_core_hash_Hash_for_hash_map_alternate_or_custom_key_types_Account_t.

Module  AccountInfo.
Section AccountInfo.
  Record t : Set := {
    name : ref str.t;
    email : ref str.t;
  }.
  
  Global Instance Get_name : Notations.Dot "name" := {
    Notations.dot := Ref.map (fun x => x.(name)) (fun v x => x <| name := v |>);
  }.
  Global Instance Get_AF_name : Notations.DoubleColon t "name" := {
    Notations.double_colon (x : M.Val t) := x.["name"];
  }.
  Global Instance Get_email : Notations.Dot "email" := {
    Notations.dot :=
      Ref.map (fun x => x.(email)) (fun v x => x <| email := v |>);
  }.
  Global Instance Get_AF_email : Notations.DoubleColon t "email" := {
    Notations.double_colon (x : M.Val t) := x.["email"];
  }.
End AccountInfo.
End AccountInfo.

Ltac Accounts :=
  exact
    (std.collections.hash.map.HashMap.t
      hash_map_alternate_or_custom_key_types.Account.t
      hash_map_alternate_or_custom_key_types.AccountInfo.t
      std.collections.hash.map.HashMap.Default.S).

(*
fn try_logon<'a>(accounts: &Accounts<'a>, username: &'a str, password: &'a str) {
    println!("Username: {}", username);
    println!("Password: {}", password);
    println!("Attempting logon...");

    let logon = Account { username, password };

    match accounts.get(&logon) {
        Some(account_info) => {
            println!("Successful logon!");
            println!("Name: {}", account_info.name);
            println!("Email: {}", account_info.email);
        }
        _ => println!("Login failed!"),
    }
}
*)
Parameter try_logon :
    (ref ltac:(hash_map_alternate_or_custom_key_types.Accounts)) ->
      (ref str.t) ->
      (ref str.t) ->
      M unit.

(*
fn main() {
    let mut accounts: Accounts = HashMap::new();

    let account = Account {
        username: "j.everyman",
        password: "password123",
    };

    let account_info = AccountInfo {
        name: "John Everyman",
        email: "j.everyman@email.com",
    };

    accounts.insert(account, account_info);

    try_logon(&accounts, "j.everyman", "psasword123");

    try_logon(&accounts, "j.everyman", "password123");
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Parameter main : M unit.