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
      clone : M.Val (ref Self) -> M (M.Val Self);
      clone_from : option (
        M.Val (mut_ref Self) ->
        M.Val (ref Self) ->
        M (M.Val unit)
      );
    }.
  End Required.

  Module Provided.
    Parameter clone_from :
      forall {Self : Set} {H0 : Required.Trait Self},
      M.Val (mut_ref Self) ->
      M.Val (ref Self) ->
      M (M.Val unit).
  End Provided.

  Class Trait (Self : Set) : Set := {
    clone :
      M.Val (ref Self) ->
      M (M.Val Self);
    clone_from :
      M.Val (mut_ref Self) ->
      M.Val (ref Self) ->
      M (M.Val unit);
  }.

  Global Instance From_Required {Self : Set}
      {H0 : Required.Trait Self} :
      Trait Self := {
    clone := Required.clone;
    clone_from := Provided.clone_from;
  }.

  Module Impl_Clone_for_str.
    Global Instance I : Trait str.t. Admitted.
  End Impl_Clone_for_str.

  Module Impl_Clone_for_Z.
    Global Instance I : Trait (M.Val Z). Admitted.
  End Impl_Clone_for_Z.
End Clone.
