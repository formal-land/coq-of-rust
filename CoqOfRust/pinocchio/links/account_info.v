Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

Require Import pinocchio.account_info.

Module Account.
    Record t : Set := {
        borrow_state : U8.t;
        is_signer: U8.t;
        is_writable: U8.t;
        executable: U8.t;
    (* key: Pubkey, *)
    (* owner: Pubkey, *)
        lamports: U64.t;
        data_len: U64.t
    }.
End Account.