Require Import CoqOfRust.lib.lib.

(* ********TRAITS******** *)
(* 
[x] Clone
*)
(* 
pub trait Clone: Sized {
    // Required method
    fn clone(&self) -> Self;

    // Provided method
    fn clone_from(&mut self, source: &Self) { ... }
}
*)
Module Clone.
  Module Required.
    Class Trait (Self : Set) : Set := {
      clone : ref Self -> M Self;
      clone_from : Datatypes.option (mut_ref Self -> ref Self -> M unit);
    }.
  End Required.

  Module Provided.
    Parameter clone_from :
      forall {Self : Set} {H0 : Required.Trait Self},
      mut_ref Self -> ref Self -> M unit.
  End Provided.

  Class Trait (Self : Set) : Set := {
    clone : ref Self -> M Self;
    clone_from : mut_ref Self -> ref Self -> M unit;
  }.

  Global Instance From_Required {Self : Set}
      {H0 : Required.Trait Self} :
      Trait Self := {
    clone := Required.clone;
    clone_from := Provided.clone_from;
  }.

  Module Impl_Clone_for_str.
    Global Instance I : Trait str. Admitted.
  End Impl_Clone_for_str.

  Module Impl_Clone_for_Z.
    Global Instance I : Trait (M.Val Z). Admitted.
  End Impl_Clone_for_Z.
End Clone.
