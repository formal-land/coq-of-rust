(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructTuple
  {
    name := "DoubleError";
    const_params := [];
    ty_params := [];
    fields := [];
  } *)

Module Impl_core_fmt_Debug_for_defining_an_error_type_DoubleError.
  Definition Self : Ty.t := Ty.path "defining_an_error_type::DoubleError".
  
  Parameter fmt : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::fmt::Debug"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
End Impl_core_fmt_Debug_for_defining_an_error_type_DoubleError.

Module Impl_core_clone_Clone_for_defining_an_error_type_DoubleError.
  Definition Self : Ty.t := Ty.path "defining_an_error_type::DoubleError".
  
  Parameter clone : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::clone::Clone"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("clone", InstanceField.Method clone) ].
End Impl_core_clone_Clone_for_defining_an_error_type_DoubleError.

Axiom Result :
  forall (T : Ty.t),
  (Ty.apply (Ty.path "defining_an_error_type::Result") [] [ T ]) =
    (Ty.apply
      (Ty.path "core::result::Result")
      []
      [ T; Ty.path "defining_an_error_type::DoubleError" ]).

Module Impl_core_fmt_Display_for_defining_an_error_type_DoubleError.
  Definition Self : Ty.t := Ty.path "defining_an_error_type::DoubleError".
  
  Parameter fmt : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::fmt::Display"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("fmt", InstanceField.Method fmt) ].
End Impl_core_fmt_Display_for_defining_an_error_type_DoubleError.

Parameter double_first : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_double_first :
  M.IsFunction.C "defining_an_error_type::double_first" double_first.
Admitted.

Parameter print : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_print : M.IsFunction.C "defining_an_error_type::print" print.
Admitted.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_main : M.IsFunction.C "defining_an_error_type::main" main.
Admitted.
