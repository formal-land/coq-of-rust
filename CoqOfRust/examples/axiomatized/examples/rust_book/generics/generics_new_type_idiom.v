(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructTuple
  {
    name := "Years";
    const_params := [];
    ty_params := [];
    fields := [ Ty.path "i64" ];
  } *)

(* StructTuple
  {
    name := "Days";
    const_params := [];
    ty_params := [];
    fields := [ Ty.path "i64" ];
  } *)

Module Impl_generics_new_type_idiom_Years.
  Definition Self : Ty.t := Ty.path "generics_new_type_idiom::Years".
  
  Parameter to_days : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_to_days : M.IsAssociatedFunction Self "to_days" to_days.
End Impl_generics_new_type_idiom_Years.

Module Impl_generics_new_type_idiom_Days.
  Definition Self : Ty.t := Ty.path "generics_new_type_idiom::Days".
  
  Parameter to_years : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_to_years : M.IsAssociatedFunction Self "to_years" to_years.
End Impl_generics_new_type_idiom_Days.

Parameter old_enough : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_old_enough : M.IsFunction "generics_new_type_idiom::old_enough" old_enough.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_main : M.IsFunction "generics_new_type_idiom::main" main.
