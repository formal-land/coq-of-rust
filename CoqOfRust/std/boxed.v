Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.alloc.

(* ********STRUCT******** *)
(* 
  [x] Box
*)
(* 
pub struct Box<T, A = Global>(_, _)
where
         A: Allocator,
         T: ?Sized;
*)
Module Box.
  Record t (T A : Set) : Set := { }.
End Box.
Definition Box (T : Set) (A : option Set) 
  `{Allocator.Trait A}
  := Box.t T (defaultType A Global).
