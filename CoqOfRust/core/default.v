Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.marker.

(* ********TRAITS******** *)
(* 
[x] Default
*)

(* 
pub trait Default: Sized {
    // Required method
    fn default() -> Self;
}
*)
Module Default.
  Class Trait `{State.Trait} (Self : Set) : Set := {
    default : M Self;
  }.
End Default.
