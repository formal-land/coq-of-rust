(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructRecord
  {
    name := "Foo";
    const_params := [ "N" ];
    ty_params := [ "T" ];
    fields := [ ("data", T); ("array", Ty.apply (Ty.path "array") [ N ] [ T ]) ];
  } *)

Module Impl_polymorphic_constants_Foo_N_A.
  Definition Self (N : Value.t) (A : Ty.t) : Ty.t :=
    Ty.apply (Ty.path "polymorphic_constants::Foo") [ N ] [ A ].
  
  Parameter convert :
      forall (N : Value.t) (A : Ty.t),
      (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom AssociatedFunction_convert :
    forall (N : Value.t) (A : Ty.t),
    M.IsAssociatedFunction (Self N A) "convert" (convert N A).
End Impl_polymorphic_constants_Foo_N_A.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Axiom Function_main : M.IsFunction "polymorphic_constants::main" main.