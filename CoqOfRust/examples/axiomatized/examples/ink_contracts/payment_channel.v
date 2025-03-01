(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructTuple
  {
    name := "AccountId";
    const_params := [];
    ty_params := [];
    fields := [ Ty.path "u128" ];
  } *)

Module Impl_core_default_Default_for_payment_channel_AccountId.
  Definition Self : Ty.t := Ty.path "payment_channel::AccountId".
  
  Parameter default : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::default::Default"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("default", InstanceField.Method default) ].
End Impl_core_default_Default_for_payment_channel_AccountId.

Module Impl_core_clone_Clone_for_payment_channel_AccountId.
  Definition Self : Ty.t := Ty.path "payment_channel::AccountId".
  
  Parameter clone : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::clone::Clone"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("clone", InstanceField.Method clone) ].
End Impl_core_clone_Clone_for_payment_channel_AccountId.

Module Impl_core_marker_Copy_for_payment_channel_AccountId.
  Definition Self : Ty.t := Ty.path "payment_channel::AccountId".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::Copy"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_Copy_for_payment_channel_AccountId.

Module Impl_core_marker_StructuralPartialEq_for_payment_channel_AccountId.
  Definition Self : Ty.t := Ty.path "payment_channel::AccountId".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::StructuralPartialEq"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_StructuralPartialEq_for_payment_channel_AccountId.

Module Impl_core_cmp_PartialEq_for_payment_channel_AccountId.
  Definition Self : Ty.t := Ty.path "payment_channel::AccountId".
  
  Parameter eq : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::cmp::PartialEq"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("eq", InstanceField.Method eq) ].
End Impl_core_cmp_PartialEq_for_payment_channel_AccountId.

Module Impl_core_cmp_Eq_for_payment_channel_AccountId.
  Definition Self : Ty.t := Ty.path "payment_channel::AccountId".
  
  Parameter assert_receiver_is_total_eq : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::cmp::Eq"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *)
      [ ("assert_receiver_is_total_eq", InstanceField.Method assert_receiver_is_total_eq) ].
End Impl_core_cmp_Eq_for_payment_channel_AccountId.

Module Impl_core_convert_From_array_Usize_32_u8_for_payment_channel_AccountId.
  Definition Self : Ty.t := Ty.path "payment_channel::AccountId".
  
  Parameter from : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::convert::From"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *)
      [ Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 32 ] [ Ty.path "u8" ] ]
      Self
      (* Instance *) [ ("from", InstanceField.Method from) ].
End Impl_core_convert_From_array_Usize_32_u8_for_payment_channel_AccountId.

Axiom Balance : (Ty.path "payment_channel::Balance") = (Ty.path "u128").

Axiom Timestamp : (Ty.path "payment_channel::Timestamp") = (Ty.path "u64").

(* StructRecord
  {
    name := "Env";
    const_params := [];
    ty_params := [];
    fields := [ ("caller", Ty.path "payment_channel::AccountId") ];
  } *)

(* StructRecord
  {
    name := "PaymentChannel";
    const_params := [];
    ty_params := [];
    fields :=
      [
        ("sender", Ty.path "payment_channel::AccountId");
        ("recipient", Ty.path "payment_channel::AccountId");
        ("expiration", Ty.apply (Ty.path "core::option::Option") [] [ Ty.path "u64" ]);
        ("withdrawn", Ty.path "u128");
        ("close_duration", Ty.path "u64")
      ];
  } *)

(*
Enum Error
{
  const_params := [];
  ty_params := [];
  variants :=
    [
      {
        name := "CallerIsNotSender";
        item := StructTuple [];
      };
      {
        name := "CallerIsNotRecipient";
        item := StructTuple [];
      };
      {
        name := "AmountIsLessThanWithdrawn";
        item := StructTuple [];
      };
      {
        name := "TransferFailed";
        item := StructTuple [];
      };
      {
        name := "NotYetExpired";
        item := StructTuple [];
      };
      {
        name := "InvalidSignature";
        item := StructTuple [];
      }
    ];
}
*)

Axiom IsDiscriminant_Error_CallerIsNotSender :
  M.IsDiscriminant "payment_channel::Error::CallerIsNotSender" 0.
Axiom IsDiscriminant_Error_CallerIsNotRecipient :
  M.IsDiscriminant "payment_channel::Error::CallerIsNotRecipient" 1.
Axiom IsDiscriminant_Error_AmountIsLessThanWithdrawn :
  M.IsDiscriminant "payment_channel::Error::AmountIsLessThanWithdrawn" 2.
Axiom IsDiscriminant_Error_TransferFailed :
  M.IsDiscriminant "payment_channel::Error::TransferFailed" 3.
Axiom IsDiscriminant_Error_NotYetExpired :
  M.IsDiscriminant "payment_channel::Error::NotYetExpired" 4.
Axiom IsDiscriminant_Error_InvalidSignature :
  M.IsDiscriminant "payment_channel::Error::InvalidSignature" 5.

Module Impl_core_marker_StructuralPartialEq_for_payment_channel_Error.
  Definition Self : Ty.t := Ty.path "payment_channel::Error".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::StructuralPartialEq"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_StructuralPartialEq_for_payment_channel_Error.

Module Impl_core_cmp_PartialEq_for_payment_channel_Error.
  Definition Self : Ty.t := Ty.path "payment_channel::Error".
  
  Parameter eq : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::cmp::PartialEq"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("eq", InstanceField.Method eq) ].
End Impl_core_cmp_PartialEq_for_payment_channel_Error.

Module Impl_core_cmp_Eq_for_payment_channel_Error.
  Definition Self : Ty.t := Ty.path "payment_channel::Error".
  
  Parameter assert_receiver_is_total_eq : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::cmp::Eq"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *)
      [ ("assert_receiver_is_total_eq", InstanceField.Method assert_receiver_is_total_eq) ].
End Impl_core_cmp_Eq_for_payment_channel_Error.

Axiom Result :
  forall (T : Ty.t),
  (Ty.apply (Ty.path "payment_channel::Result") [] [ T ]) =
    (Ty.apply (Ty.path "core::result::Result") [] [ T; Ty.path "payment_channel::Error" ]).

(* StructRecord
  {
    name := "SenderCloseStarted";
    const_params := [];
    ty_params := [];
    fields := [ ("expiration", Ty.path "u64"); ("close_duration", Ty.path "u64") ];
  } *)

(*
Enum Event
{
  const_params := [];
  ty_params := [];
  variants :=
    [
      {
        name := "SenderCloseStarted";
        item := StructTuple [ Ty.path "payment_channel::SenderCloseStarted" ];
      }
    ];
}
*)

Axiom IsDiscriminant_Event_SenderCloseStarted :
  M.IsDiscriminant "payment_channel::Event::SenderCloseStarted" 0.

Module Impl_payment_channel_Env.
  Definition Self : Ty.t := Ty.path "payment_channel::Env".
  
  Parameter caller : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_caller : M.IsAssociatedFunction Self "caller" caller.
  Smpl Add apply AssociatedFunction_caller : is_associated.
  
  Parameter emit_event : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_emit_event : M.IsAssociatedFunction Self "emit_event" emit_event.
  Smpl Add apply AssociatedFunction_emit_event : is_associated.
  
  Parameter terminate_contract : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_terminate_contract :
    M.IsAssociatedFunction Self "terminate_contract" terminate_contract.
  Smpl Add apply AssociatedFunction_terminate_contract : is_associated.
  
  Parameter transfer : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_transfer : M.IsAssociatedFunction Self "transfer" transfer.
  Smpl Add apply AssociatedFunction_transfer : is_associated.
  
  Parameter block_timestamp : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_block_timestamp :
    M.IsAssociatedFunction Self "block_timestamp" block_timestamp.
  Smpl Add apply AssociatedFunction_block_timestamp : is_associated.
  
  Parameter balance : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_balance : M.IsAssociatedFunction Self "balance" balance.
  Smpl Add apply AssociatedFunction_balance : is_associated.
  
  Parameter account_id : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_account_id : M.IsAssociatedFunction Self "account_id" account_id.
  Smpl Add apply AssociatedFunction_account_id : is_associated.
End Impl_payment_channel_Env.

(* Trait *)
(* Empty module 'HashOutput' *)

(* Trait *)
(* Empty module 'CryptoHash' *)

Parameter hash_encoded : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_hash_encoded : M.IsFunction "payment_channel::hash_encoded" hash_encoded.
Smpl Add apply Function_hash_encoded : is_function.

Parameter ecdsa_recover : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_ecdsa_recover : M.IsFunction "payment_channel::ecdsa_recover" ecdsa_recover.
Smpl Add apply Function_ecdsa_recover : is_function.

(*
Enum Sha2x256
{
  const_params := [];
  ty_params := [];
  variants := [];
}
*)


(*
Enum Keccak256
{
  const_params := [];
  ty_params := [];
  variants := [];
}
*)


(*
Enum Blake2x256
{
  const_params := [];
  ty_params := [];
  variants := [];
}
*)


(*
Enum Blake2x128
{
  const_params := [];
  ty_params := [];
  variants := [];
}
*)


Module Impl_payment_channel_HashOutput_for_payment_channel_Sha2x256.
  Definition Self : Ty.t := Ty.path "payment_channel::Sha2x256".
  
  Definition _Type_ : Ty.t :=
    Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 32 ] [ Ty.path "u8" ].
  
  Axiom Implements :
    M.IsTraitInstance
      "payment_channel::HashOutput"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("Type_", InstanceField.Ty _Type_) ].
End Impl_payment_channel_HashOutput_for_payment_channel_Sha2x256.

Module Impl_payment_channel_HashOutput_for_payment_channel_Keccak256.
  Definition Self : Ty.t := Ty.path "payment_channel::Keccak256".
  
  Definition _Type_ : Ty.t :=
    Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 32 ] [ Ty.path "u8" ].
  
  Axiom Implements :
    M.IsTraitInstance
      "payment_channel::HashOutput"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("Type_", InstanceField.Ty _Type_) ].
End Impl_payment_channel_HashOutput_for_payment_channel_Keccak256.

Module Impl_payment_channel_HashOutput_for_payment_channel_Blake2x256.
  Definition Self : Ty.t := Ty.path "payment_channel::Blake2x256".
  
  Definition _Type_ : Ty.t :=
    Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 32 ] [ Ty.path "u8" ].
  
  Axiom Implements :
    M.IsTraitInstance
      "payment_channel::HashOutput"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("Type_", InstanceField.Ty _Type_) ].
End Impl_payment_channel_HashOutput_for_payment_channel_Blake2x256.

Module Impl_payment_channel_HashOutput_for_payment_channel_Blake2x128.
  Definition Self : Ty.t := Ty.path "payment_channel::Blake2x128".
  
  Definition _Type_ : Ty.t :=
    Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 16 ] [ Ty.path "u8" ].
  
  Axiom Implements :
    M.IsTraitInstance
      "payment_channel::HashOutput"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("Type_", InstanceField.Ty _Type_) ].
End Impl_payment_channel_HashOutput_for_payment_channel_Blake2x128.

Module Impl_payment_channel_CryptoHash_for_payment_channel_Sha2x256.
  Definition Self : Ty.t := Ty.path "payment_channel::Sha2x256".
  
  Parameter hash : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "payment_channel::CryptoHash"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("hash", InstanceField.Method hash) ].
End Impl_payment_channel_CryptoHash_for_payment_channel_Sha2x256.

Module Impl_payment_channel_CryptoHash_for_payment_channel_Keccak256.
  Definition Self : Ty.t := Ty.path "payment_channel::Keccak256".
  
  Parameter hash : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "payment_channel::CryptoHash"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("hash", InstanceField.Method hash) ].
End Impl_payment_channel_CryptoHash_for_payment_channel_Keccak256.

Module Impl_payment_channel_CryptoHash_for_payment_channel_Blake2x256.
  Definition Self : Ty.t := Ty.path "payment_channel::Blake2x256".
  
  Parameter hash : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "payment_channel::CryptoHash"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("hash", InstanceField.Method hash) ].
End Impl_payment_channel_CryptoHash_for_payment_channel_Blake2x256.

Module Impl_payment_channel_CryptoHash_for_payment_channel_Blake2x128.
  Definition Self : Ty.t := Ty.path "payment_channel::Blake2x128".
  
  Parameter hash : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "payment_channel::CryptoHash"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("hash", InstanceField.Method hash) ].
End Impl_payment_channel_CryptoHash_for_payment_channel_Blake2x128.

Module Impl_payment_channel_PaymentChannel.
  Definition Self : Ty.t := Ty.path "payment_channel::PaymentChannel".
  
  Parameter init_env : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_init_env : M.IsAssociatedFunction Self "init_env" init_env.
  Smpl Add apply AssociatedFunction_init_env : is_associated.
  
  Parameter env : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_env : M.IsAssociatedFunction Self "env" env.
  Smpl Add apply AssociatedFunction_env : is_associated.
  
  Parameter is_signature_valid : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_is_signature_valid :
    M.IsAssociatedFunction Self "is_signature_valid" is_signature_valid.
  Smpl Add apply AssociatedFunction_is_signature_valid : is_associated.
  
  Parameter new : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_new : M.IsAssociatedFunction Self "new" new.
  Smpl Add apply AssociatedFunction_new : is_associated.
  
  Parameter close_inner : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_close_inner : M.IsAssociatedFunction Self "close_inner" close_inner.
  Smpl Add apply AssociatedFunction_close_inner : is_associated.
  
  Parameter close : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_close : M.IsAssociatedFunction Self "close" close.
  Smpl Add apply AssociatedFunction_close : is_associated.
  
  Parameter start_sender_close : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_start_sender_close :
    M.IsAssociatedFunction Self "start_sender_close" start_sender_close.
  Smpl Add apply AssociatedFunction_start_sender_close : is_associated.
  
  Parameter claim_timeout : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_claim_timeout :
    M.IsAssociatedFunction Self "claim_timeout" claim_timeout.
  Smpl Add apply AssociatedFunction_claim_timeout : is_associated.
  
  Parameter withdraw : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_withdraw : M.IsAssociatedFunction Self "withdraw" withdraw.
  Smpl Add apply AssociatedFunction_withdraw : is_associated.
  
  Parameter get_sender : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_get_sender : M.IsAssociatedFunction Self "get_sender" get_sender.
  Smpl Add apply AssociatedFunction_get_sender : is_associated.
  
  Parameter get_recipient : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_get_recipient :
    M.IsAssociatedFunction Self "get_recipient" get_recipient.
  Smpl Add apply AssociatedFunction_get_recipient : is_associated.
  
  Parameter get_expiration : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_get_expiration :
    M.IsAssociatedFunction Self "get_expiration" get_expiration.
  Smpl Add apply AssociatedFunction_get_expiration : is_associated.
  
  Parameter get_withdrawn : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_get_withdrawn :
    M.IsAssociatedFunction Self "get_withdrawn" get_withdrawn.
  Smpl Add apply AssociatedFunction_get_withdrawn : is_associated.
  
  Parameter get_close_duration : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_get_close_duration :
    M.IsAssociatedFunction Self "get_close_duration" get_close_duration.
  Smpl Add apply AssociatedFunction_get_close_duration : is_associated.
  
  Parameter get_balance : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_get_balance : M.IsAssociatedFunction Self "get_balance" get_balance.
  Smpl Add apply AssociatedFunction_get_balance : is_associated.
End Impl_payment_channel_PaymentChannel.
