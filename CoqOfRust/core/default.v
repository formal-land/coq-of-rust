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
  Class Trait (Self : Set) : Set := {
    default `{H : State.Trait} : M Self;
  }.
End Default.
