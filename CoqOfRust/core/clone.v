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
  Class Trait (Self : Set) `{H : State.Trait} : Set := {
    clone : ref Self -> M (H := H) Self;
  }.

  Global Instance Method_clone `{State.Trait} `(Trait) : Notation.Dot "clone" := {
    Notation.dot := clone;
  }.

  Module Impl_Clone_for_str.
    Global Instance I `{State.Trait} : Trait str. Admitted.
  End Impl_Clone_for_str.

  Module Impl_Clone_for_Z.
    Global Instance I `{State.Trait} : Trait (M.val Z). Admitted.
  End Impl_Clone_for_Z.
End Clone.
