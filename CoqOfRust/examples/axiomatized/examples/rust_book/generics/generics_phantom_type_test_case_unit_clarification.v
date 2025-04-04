(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
Enum Inch
{
  const_params := [];
  ty_params := [];
  variants := [];
}
*)


Module Impl_core_fmt_Debug_for_generics_phantom_type_test_case_unit_clarification_Inch.
  Definition Self : Ty.t := Ty.path "generics_phantom_type_test_case_unit_clarification::Inch".
  
  Parameter fmt : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::fmt::Debug"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
End Impl_core_fmt_Debug_for_generics_phantom_type_test_case_unit_clarification_Inch.

Module Impl_core_clone_Clone_for_generics_phantom_type_test_case_unit_clarification_Inch.
  Definition Self : Ty.t := Ty.path "generics_phantom_type_test_case_unit_clarification::Inch".
  
  Parameter clone : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::clone::Clone"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("clone", InstanceField.Method clone) ].
End Impl_core_clone_Clone_for_generics_phantom_type_test_case_unit_clarification_Inch.

Module Impl_core_marker_Copy_for_generics_phantom_type_test_case_unit_clarification_Inch.
  Definition Self : Ty.t := Ty.path "generics_phantom_type_test_case_unit_clarification::Inch".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::Copy"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_Copy_for_generics_phantom_type_test_case_unit_clarification_Inch.

(*
Enum Mm
{
  const_params := [];
  ty_params := [];
  variants := [];
}
*)


Module Impl_core_fmt_Debug_for_generics_phantom_type_test_case_unit_clarification_Mm.
  Definition Self : Ty.t := Ty.path "generics_phantom_type_test_case_unit_clarification::Mm".
  
  Parameter fmt : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::fmt::Debug"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
End Impl_core_fmt_Debug_for_generics_phantom_type_test_case_unit_clarification_Mm.

Module Impl_core_clone_Clone_for_generics_phantom_type_test_case_unit_clarification_Mm.
  Definition Self : Ty.t := Ty.path "generics_phantom_type_test_case_unit_clarification::Mm".
  
  Parameter clone : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::clone::Clone"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("clone", InstanceField.Method clone) ].
End Impl_core_clone_Clone_for_generics_phantom_type_test_case_unit_clarification_Mm.

Module Impl_core_marker_Copy_for_generics_phantom_type_test_case_unit_clarification_Mm.
  Definition Self : Ty.t := Ty.path "generics_phantom_type_test_case_unit_clarification::Mm".
  
  Axiom Implements :
    M.IsTraitInstance
      "core::marker::Copy"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [].
End Impl_core_marker_Copy_for_generics_phantom_type_test_case_unit_clarification_Mm.

(* StructTuple
  {
    name := "Length";
    const_params := [];
    ty_params := [ "Unit" ];
    fields := [ Ty.path "f64"; Ty.apply (Ty.path "core::marker::PhantomData") [] [ Unit ] ];
  } *)

Module Impl_core_fmt_Debug_where_core_fmt_Debug_Unit_for_generics_phantom_type_test_case_unit_clarification_Length_Unit.
  Definition Self (Unit : Ty.t) : Ty.t :=
    Ty.apply (Ty.path "generics_phantom_type_test_case_unit_clarification::Length") [] [ Unit ].
  
  Parameter fmt : forall (Unit : Ty.t), (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    forall (Unit : Ty.t),
    M.IsTraitInstance
      "core::fmt::Debug"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      (Self Unit)
      (* Instance *) [ ("fmt", InstanceField.Method (fmt Unit)) ].
End Impl_core_fmt_Debug_where_core_fmt_Debug_Unit_for_generics_phantom_type_test_case_unit_clarification_Length_Unit.

Module Impl_core_clone_Clone_where_core_clone_Clone_Unit_for_generics_phantom_type_test_case_unit_clarification_Length_Unit.
  Definition Self (Unit : Ty.t) : Ty.t :=
    Ty.apply (Ty.path "generics_phantom_type_test_case_unit_clarification::Length") [] [ Unit ].
  
  Parameter clone : forall (Unit : Ty.t), (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    forall (Unit : Ty.t),
    M.IsTraitInstance
      "core::clone::Clone"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      (Self Unit)
      (* Instance *) [ ("clone", InstanceField.Method (clone Unit)) ].
End Impl_core_clone_Clone_where_core_clone_Clone_Unit_for_generics_phantom_type_test_case_unit_clarification_Length_Unit.

Module Impl_core_marker_Copy_where_core_marker_Copy_Unit_for_generics_phantom_type_test_case_unit_clarification_Length_Unit.
  Definition Self (Unit : Ty.t) : Ty.t :=
    Ty.apply (Ty.path "generics_phantom_type_test_case_unit_clarification::Length") [] [ Unit ].
  
  Axiom Implements :
    forall (Unit : Ty.t),
    M.IsTraitInstance
      "core::marker::Copy"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      (Self Unit)
      (* Instance *) [].
End Impl_core_marker_Copy_where_core_marker_Copy_Unit_for_generics_phantom_type_test_case_unit_clarification_Length_Unit.

Module Impl_core_ops_arith_Add_generics_phantom_type_test_case_unit_clarification_Length_Unit_for_generics_phantom_type_test_case_unit_clarification_Length_Unit.
  Definition Self (Unit : Ty.t) : Ty.t :=
    Ty.apply (Ty.path "generics_phantom_type_test_case_unit_clarification::Length") [] [ Unit ].
  
  Definition _Output (Unit : Ty.t) : Ty.t :=
    Ty.apply (Ty.path "generics_phantom_type_test_case_unit_clarification::Length") [] [ Unit ].
  
  Parameter add : forall (Unit : Ty.t), (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    forall (Unit : Ty.t),
    M.IsTraitInstance
      "core::ops::arith::Add"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *)
      [ Ty.apply (Ty.path "generics_phantom_type_test_case_unit_clarification::Length") [] [ Unit ]
      ]
      (Self Unit)
      (* Instance *)
      [ ("Output", InstanceField.Ty (_Output Unit)); ("add", InstanceField.Method (add Unit)) ].
End Impl_core_ops_arith_Add_generics_phantom_type_test_case_unit_clarification_Length_Unit_for_generics_phantom_type_test_case_unit_clarification_Length_Unit.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_main :
  M.IsFunction.C "generics_phantom_type_test_case_unit_clarification::main" main.
Admitted.
