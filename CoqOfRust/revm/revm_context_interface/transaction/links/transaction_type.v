Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.cmp.

(*
pub enum TransactionType {
    Legacy,
    Eip2930,
    Eip1559,
    Eip4844,
    Eip7702,
    Custom,
}
*)
Module TransactionType.
  Inductive t : Set :=
  | Legacy
  | Eip2930
  | Eip1559
  | Eip4844
  | Eip7702
  | Custom.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_context_interface::transaction::transaction_type::TransactionType";
    φ x :=
      match x with
      | Legacy => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" []
      | Eip2930 => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" []
      | Eip1559 => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" []
      | Eip4844 => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" []
      | Eip7702 => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" []
      | Custom => Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" []
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_context_interface::transaction::transaction_type::TransactionType").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Legacy :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" [] = φ Legacy.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Legacy : of_value.

  Lemma of_value_with_Eip2930 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" [] = φ Eip2930.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Eip2930 : of_value.

  Lemma of_value_with_Eip1559 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" [] = φ Eip1559.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Eip1559 : of_value.

  Lemma of_value_with_Eip4844 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" [] = φ Eip4844.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Eip4844 : of_value.

  Lemma of_value_with_Eip7702 :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" [] = φ Eip7702.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Eip7702 : of_value.

  Lemma of_value_with_Custom :
    Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" [] = φ Custom.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Custom : of_value.

  Definition of_value_Legacy :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Legacy" []).
  Proof. econstructor; apply of_value_with_Legacy. Defined.
  Smpl Add apply of_value_Legacy : of_value.

  Definition of_value_Eip2930 :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip2930" []).
  Proof. econstructor; apply of_value_with_Eip2930. Defined.
  Smpl Add apply of_value_Eip2930 : of_value.

  Definition of_value_Eip1559 :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip1559" []).
  Proof. econstructor; apply of_value_with_Eip1559. Defined.
  Smpl Add apply of_value_Eip1559 : of_value.

  Definition of_value_Eip4844 :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip4844" []).
  Proof. econstructor; apply of_value_with_Eip4844. Defined.
  Smpl Add apply of_value_Eip4844 : of_value.

  Definition of_value_Eip7702 :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Eip7702" []).
  Proof. econstructor; apply of_value_with_Eip7702. Defined.
  Smpl Add apply of_value_Eip7702 : of_value.

  Definition of_value_Custom :
    OfValue.t (Value.StructTuple "revm_context_interface::transaction::transaction_type::TransactionType::Custom" []).
  Proof. econstructor; apply of_value_with_Custom. Defined.
  Smpl Add apply of_value_Custom : of_value.
End TransactionType.

Module Impl_PartialEq_for_TransactionType.
  Definition Self : Set := TransactionType.t.

  Instance run : PartialEq.Run Self Self.
  Admitted.
End Impl_PartialEq_for_TransactionType.
