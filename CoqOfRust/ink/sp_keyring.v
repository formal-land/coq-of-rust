(* Written by hand *)
Require Import CoqOfRust.CoqOfRust.

(* TODO: Implement the followings to satisfy the dependency:
- [x] sr25519.Keyring
*)

(* 
pub enum Keyring {
    Alice,
    Bob,
    Charlie,
    Dave,
    Eve,
    Ferdie,
    One,
    Two,
}
*)
Module sr25519.
  Module Keyring.
    Inductive t : Set := 
    | Alice
    | Bob
    | Charlie
    | Dave
    | Eve
    | Ferdie
    | One
    | Two
    .
  End Keyring.
  Definition Keyring := Keyring.t.
End sr25519.
