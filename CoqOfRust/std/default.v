Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.marker.

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
    default : Self;
  }.
End Default.
