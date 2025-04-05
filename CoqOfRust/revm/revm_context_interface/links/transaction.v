Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.links.aliases.
Require Import alloy_primitives.links.common.
Require Import core.convert.links.mod.
Require Import core.links.error.
Require Import core.links.option.
Require Import revm.revm_context_interface.transaction.links.eip4844.
Require Import revm.revm_context_interface.transaction.links.transaction_type.

(* pub trait TransactionError: Debug + core::error::Error {} *)
Module TransactionError.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::transaction::TransactionError", [], [], Φ Self).

  Class Run (Self : Set) `{Link Self} : Set := {
    run_Error_for_Self : Error.Run Self;
  }.
End TransactionError.

(*
pub trait Transaction {
    type TransactionError: TransactionError;
    type TransactionType: Into<TransactionType>;
    type AccessList: AccessListTrait;
    type Legacy: LegacyTx;
    type Eip2930: Eip2930Tx<AccessList = Self::AccessList>;
    type Eip1559: Eip1559Tx<AccessList = Self::AccessList>;
    type Eip4844: Eip4844Tx<AccessList = Self::AccessList>;
    type Eip7702: Eip7702Tx<AccessList = Self::AccessList>;

    fn tx_type(&self) -> Self::TransactionType;
    fn legacy(&self) -> &Self::Legacy;
    fn eip2930(&self) -> &Self::Eip2930;
    fn eip1559(&self) -> &Self::Eip1559;
    fn eip4844(&self) -> &Self::Eip4844;
    fn eip7702(&self) -> &Self::Eip7702;
    fn common_fields(&self) -> &dyn CommonTxFields
    fn max_fee(&self) -> u128
    fn effective_gas_price(&self, base_fee: u128) -> u128
    fn kind(&self) -> TxKind
    fn access_list(&self) -> Option<&Self::AccessList>
}
*)
Module Transaction.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::transaction::Transaction", [], [], Φ Self).

  Module Types.
    Record t : Type := {
      TransactionError : Set;
      TransactionType : Set;
      AccessList : Set;
      Legacy : Set;
      Eip2930 : Set;
      Eip1559 : Set;
      Eip4844 : Set;
      Eip7702 : Set;
    }.

    Class AreLinks (types : t) : Set := {
      H_TransactionError : Link types.(TransactionError);
      H_TransactionType : Link types.(TransactionType);
      H_AccessList : Link types.(AccessList);
      H_Legacy : Link types.(Legacy);
      H_Eip2930 : Link types.(Eip2930);
      H_Eip1559 : Link types.(Eip1559);
      H_Eip4844 : Link types.(Eip4844);
      H_Eip7702 : Link types.(Eip7702);
    }.

    Global Instance IsLinkTransactionError (types : t) (H : AreLinks types) : Link types.(TransactionError) :=
      H.(H_TransactionError _).
    Global Instance IsLinkTransactionType (types : t) (H : AreLinks types) : Link types.(TransactionType) :=
      H.(H_TransactionType _).
    Global Instance IsLinkAccessList (types : t) (H : AreLinks types) : Link types.(AccessList) :=
      H.(H_AccessList _).
    Global Instance IsLinkLegacy (types : t) (H : AreLinks types) : Link types.(Legacy) :=
      H.(H_Legacy _).
    Global Instance IsLinkEip2930 (types : t) (H : AreLinks types) : Link types.(Eip2930) :=
      H.(H_Eip2930 _).
    Global Instance IsLinkEip1559 (types : t) (H : AreLinks types) : Link types.(Eip1559) :=
      H.(H_Eip1559 _).
    Global Instance IsLinkEip4844 (types : t) (H : AreLinks types) : Link types.(Eip4844) :=
      H.(H_Eip4844 _).
    Global Instance IsLinkEip7702 (types : t) (H : AreLinks types) : Link types.(Eip7702) :=
      H.(H_Eip7702 _).
  End Types.

  Definition Run_tx_type
    (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
    TraitMethod.C (trait Self) "tx_type" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] types.(Types.TransactionType)
    ).

  Definition Run_legacy
    (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
    TraitMethod.C (trait Self) "legacy" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref types.(Types.Legacy))
    ).

  Definition Run_eip2930
    (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
    TraitMethod.C (trait Self) "eip2930" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref types.(Types.Eip2930))
    ).

  Definition Run_eip1559
    (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
    TraitMethod.C (trait Self) "eip1559" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref types.(Types.Eip1559))
    ).

  Definition Run_eip4844
    (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
    TraitMethod.C (trait Self) "eip4844" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref types.(Types.Eip4844))
    ).

  Definition Run_eip7702
    (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
    TraitMethod.C (trait Self) "eip7702" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref types.(Types.Eip7702))
    ).

  (* Definition Run_common_fields
    (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
    TraitMethod.C (trait Self) "common_fields" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref types.(Types.CommonTxFields))
    ). *)

  Definition Run_max_fee
    (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
    TraitMethod.C (trait Self) "max_fee" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] U128.t
    ).

  Definition Run_effective_gas_price
    (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
    TraitMethod.C (trait Self) "effective_gas_price" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (base_fee : U128.t),
      Run.Trait method [] [] [ φ self; φ base_fee ] U128.t
    ).

  Definition Run_kind
    (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
    TraitMethod.C (trait Self) "kind" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] TxKind.t
    ).

  Definition Run_access_list
    (Self : Set) `{Link Self}
    (types : Types.t) `{Types.AreLinks types} :
    Set :=
    TraitMethod.C (trait Self) "access_list" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (option (Ref.t Pointer.Kind.Ref types.(Types.AccessList)))
    ).

  Class Run
      (Self : Set) `{Link Self}
      (types : Types.t) `{Types.AreLinks types} :
      Set := {
    TransactionError_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "TransactionError" (Φ types.(Types.TransactionError));
    TransactionType_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "TransactionType" (Φ types.(Types.TransactionType));
    run_Into_for_TransactionType :
      Into.Run types.(Types.TransactionType) TransactionType.t;
    AccessList_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "AccessList" (Φ types.(Types.AccessList));
    Legacy_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "Legacy" (Φ types.(Types.Legacy));
    Eip2930_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "Eip2930" (Φ types.(Types.Eip2930));
    Eip1559_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "Eip1559" (Φ types.(Types.Eip1559));
    Eip4844_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "Eip4844" (Φ types.(Types.Eip4844));
    run_Eip4844Tx_for_Eip4844 : Eip4844Tx.Run types.(Types.Eip4844);
    Eip7702_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::Transaction" [] [] (Φ Self)
        "Eip7702" (Φ types.(Types.Eip7702));
    tx_type : Run_tx_type Self types;
    legacy : Run_legacy Self types;
    eip2930 : Run_eip2930 Self types;
    eip1559 : Run_eip1559 Self types;
    eip4844 : Run_eip4844 Self types;
    eip7702 : Run_eip7702 Self types;
    (* common_fields : Run_common_fields Self types; *)
    max_fee : Run_max_fee Self types;
    effective_gas_price : Run_effective_gas_price Self types;
    kind : Run_kind Self types;
    access_list : Run_access_list Self types;
  }.
End Transaction.

Module Impl_Transaction_for_Ref_Transaction.
  Instance run
    (Self : Set) `{Link Self}
    (types : Transaction.Types.t) `{Transaction.Types.AreLinks types}
    (run_Transaction_for_Self : Transaction.Run Self types) :
    Transaction.Run (Ref.t Pointer.Kind.Ref Self) types.
  Admitted.
End Impl_Transaction_for_Ref_Transaction.

(*
pub trait TransactionGetter {
    type Transaction: Transaction;

    fn tx(&self) -> &Self::Transaction;
}
*)
Module TransactionGetter.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::transaction::TransactionGetter", [], [], Φ Self).

  Definition Run_tx
    (Self : Set) `{Link Self}
    (Transaction : Set) `{Link Transaction} :
    Set :=
    TraitMethod.C (trait Self) "tx" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref Transaction)
    ).

  Class Run
      (Self : Set) `{Link Self}
      (Transaction : Set) `{Link Transaction}
      (types : Transaction.Types.t) `{Transaction.Types.AreLinks types} :
      Set := {
    Transaction_IsAssociated :
      IsTraitAssociatedType
        "revm_context_interface::transaction::TransactionGetter" [] [] (Φ Self)
        "Transaction" (Φ Transaction);
    run_Transaction_for_Transaction :
      Transaction.Run Transaction types;
    tx : Run_tx Self Transaction;
  }.
End TransactionGetter.

(*
pub trait TransactionSetter: TransactionGetter {
    fn set_tx(&mut self, tx: <Self as TransactionGetter>::Transaction);
}
*)
Module TransactionSetter.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("revm_context_interface::transaction::TransactionSetter", [], [], Φ Self).

  Definition Run_set_tx
    (Self : Set) `{Link Self}
    (Transaction : Set) `{Link Transaction} :
    Set :=
    TraitMethod.C (trait Self) "set_tx" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (tx : Transaction),
      Run.Trait method [] [] [ φ self; φ tx ] unit
    ).

  Class Run
      (Self : Set) `{Link Self}
      (Transaction : Set) `{Link Transaction}
      (types : Transaction.Types.t) `{Transaction.Types.AreLinks types} :
      Set := {
    run_TransactionGetter_for_Self :
      TransactionGetter.Run Self Transaction types;
    set_tx : Run_set_tx Self Transaction;
  }.
End TransactionSetter.
