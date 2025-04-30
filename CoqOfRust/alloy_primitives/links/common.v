Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.bits.links.address.
Require Import alloy_primitives.common.

(*
pub enum TxKind {
    Create,
    Call(Address),
}
*)
Module TxKind.
  Inductive t : Set :=
  | Create
  | Call (address : Address.t).

  Global Instance IsLink : Link t := {
    Φ := Ty.path "alloy_primitives::common::TxKind";
    φ x :=
      match x with
      | Create => Value.StructTuple "alloy_primitives::common::TxKind::Create" [] [] []
      | Call address => Value.StructTuple "alloy_primitives::common::TxKind::Call" [] [] [φ address]
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "alloy_primitives::common::TxKind").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.
End TxKind.
