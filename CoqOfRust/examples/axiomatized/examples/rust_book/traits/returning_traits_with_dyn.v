(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(* StructTuple
  {
    name := "Sheep";
    const_params := [];
    ty_params := [];
    fields := [];
  } *)

(* StructTuple
  {
    name := "Cow";
    const_params := [];
    ty_params := [];
    fields := [];
  } *)

(* Trait *)
(* Empty module 'Animal' *)

Module Impl_returning_traits_with_dyn_Animal_for_returning_traits_with_dyn_Sheep.
  Definition Self : Ty.t := Ty.path "returning_traits_with_dyn::Sheep".
  
  Parameter noise : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "returning_traits_with_dyn::Animal"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("noise", InstanceField.Method noise) ].
End Impl_returning_traits_with_dyn_Animal_for_returning_traits_with_dyn_Sheep.

Module Impl_returning_traits_with_dyn_Animal_for_returning_traits_with_dyn_Cow.
  Definition Self : Ty.t := Ty.path "returning_traits_with_dyn::Cow".
  
  Parameter noise : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.
  
  Axiom Implements :
    M.IsTraitInstance
      "returning_traits_with_dyn::Animal"
      (* Trait polymorphic consts *) []
      (* Trait polymorphic types *) []
      Self
      (* Instance *) [ ("noise", InstanceField.Method noise) ].
End Impl_returning_traits_with_dyn_Animal_for_returning_traits_with_dyn_Cow.

Parameter random_animal : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_random_animal :
  M.IsFunction.C "returning_traits_with_dyn::random_animal" random_animal.
Admitted.

Parameter main : (list Value.t) -> (list Ty.t) -> (list Value.t) -> M.

Global Instance Instance_IsFunction_main : M.IsFunction.C "returning_traits_with_dyn::main" main.
Admitted.
