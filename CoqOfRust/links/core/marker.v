(* Generated file for the links. Do not edit. *)
Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Import Run.

Module PhantomData.
  Inductive t (T: Set) `{Link T} : Set :=
  | Make : t T.
End PhantomData.
