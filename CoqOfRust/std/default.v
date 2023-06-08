Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.marker.

(* ********TRAITS******** *)
(* 
[x] Default
*)

(* NOTE: Can we utilize this trait to translate those type params with default type? *)
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
