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
  Class Trait (Self : Set) : Set := {
    clone `{H : State.Trait} : ref Self -> M (H := H) Self;
  }.

  Module Impl_Clone_for_str.
    Global Instance I : Trait str. Admitted.
  End Impl_Clone_for_str.
End Clone.
