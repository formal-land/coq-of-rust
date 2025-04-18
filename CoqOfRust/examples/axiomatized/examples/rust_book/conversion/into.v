(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructRecord
  {
    name := "Number";
    const_params := [];
    ty_params := [];
    fields := [ ("value", Ty.path "i32") ];
  } *)

Module Impl_core_convert_From_i32_for_into_Number.
  Definition Self : Ty.t := Ty.path "into::Number".
  
  Parameter from : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "core::convert::From"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) [ Ty.path "i32" ]
      Self
      (* Instance *) [ ("from", InstanceField.Method from) ].
End Impl_core_convert_From_i32_for_into_Number.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_main : M.IsFunction.C "into::main" main.
Admitted.
