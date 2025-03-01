(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructTuple
  {
    name := "AccountId";
    const_params := [];
    ty_params := [];
    fields := [ Ty.path "u128" ];
  } *)

Module Impl_core_default_Default_for_contract_ref_AccountId.
  Definition Self : Ty.t := Ty.path "contract_ref::AccountId".
  
  Parameter default : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::default::Default"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("default", InstanceField.Method default) ].
End Impl_core_default_Default_for_contract_ref_AccountId.

Module Impl_core_clone_Clone_for_contract_ref_AccountId.
  Definition Self : Ty.t := Ty.path "contract_ref::AccountId".
  
  Parameter clone : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::clone::Clone"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("clone", InstanceField.Method clone) ].
End Impl_core_clone_Clone_for_contract_ref_AccountId.

Module Impl_core_marker_Copy_for_contract_ref_AccountId.
  Definition Self : Ty.t := Ty.path "contract_ref::AccountId".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::Copy"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_Copy_for_contract_ref_AccountId.

Axiom Balance : (Ty.path "contract_ref::Balance") = (Ty.path "u128").

Axiom Hash :
  (Ty.path "contract_ref::Hash") =
    (Ty.apply (Ty.path "array") [ Value.Integer IntegerKind.Usize 32 ] [ Ty.path "u8" ]).

(* StructRecord
  {
    name := "Env";
    const_params := [];
    ty_params := [];
    fields := [ ("caller", Ty.path "contract_ref::AccountId") ];
  } *)

(* StructRecord
  {
    name := "FlipperRef";
    const_params := [];
    ty_params := [];
    fields := [ ("value", Ty.path "bool") ];
  } *)

(* StructTuple
  {
    name := "FlipperError";
    const_params := [];
    ty_params := [];
    fields := [];
  } *)

Module Impl_core_fmt_Debug_for_contract_ref_FlipperError.
  Definition Self : Ty.t := Ty.path "contract_ref::FlipperError".
  
  Parameter fmt : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::fmt::Debug"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
End Impl_core_fmt_Debug_for_contract_ref_FlipperError.

Module Impl_contract_ref_FlipperRef.
  Definition Self : Ty.t := Ty.path "contract_ref::FlipperRef".
  
  Parameter init_env : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_init_env : M.IsAssociatedFunction Self "init_env" init_env.
  Smpl Add apply AssociatedFunction_init_env : is_associated.
  
  Parameter env : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_env : M.IsAssociatedFunction Self "env" env.
  Smpl Add apply AssociatedFunction_env : is_associated.
  
  Parameter new : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_new : M.IsAssociatedFunction Self "new" new.
  Smpl Add apply AssociatedFunction_new : is_associated.
  
  Parameter new_default : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_new_default : M.IsAssociatedFunction Self "new_default" new_default.
  Smpl Add apply AssociatedFunction_new_default : is_associated.
  
  Parameter try_new : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_try_new : M.IsAssociatedFunction Self "try_new" try_new.
  Smpl Add apply AssociatedFunction_try_new : is_associated.
  
  Parameter flip : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_flip : M.IsAssociatedFunction Self "flip" flip.
  Smpl Add apply AssociatedFunction_flip : is_associated.
  
  Parameter get : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_get : M.IsAssociatedFunction Self "get" get.
  Smpl Add apply AssociatedFunction_get : is_associated.
End Impl_contract_ref_FlipperRef.

(* StructRecord
  {
    name := "ContractRef";
    const_params := [];
    ty_params := [];
    fields := [ ("flipper", Ty.path "contract_ref::FlipperRef") ];
  } *)

Module Impl_contract_ref_ContractRef.
  Definition Self : Ty.t := Ty.path "contract_ref::ContractRef".
  
  Parameter new : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_new : M.IsAssociatedFunction Self "new" new.
  Smpl Add apply AssociatedFunction_new : is_associated.
  
  Parameter try_new : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_try_new : M.IsAssociatedFunction Self "try_new" try_new.
  Smpl Add apply AssociatedFunction_try_new : is_associated.
  
  Parameter flip : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_flip : M.IsAssociatedFunction Self "flip" flip.
  Smpl Add apply AssociatedFunction_flip : is_associated.
  
  Parameter get : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_get : M.IsAssociatedFunction Self "get" get.
  Smpl Add apply AssociatedFunction_get : is_associated.
End Impl_contract_ref_ContractRef.
