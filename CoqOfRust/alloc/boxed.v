Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.alloc.

(* ********STRUCTS******** *)
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
  Definition t (T (*A*) : Set) : Set := T.
End Box.
Definition Box (T : Set) (*(A : option Set)
  `{Allocator.Trait (defaultType A Global)}*)
  := Box.t T (*(defaultType A Global)*).

Parameter new :
  forall `{State.Trait} {A : Set},
  A -> M (Box A (*None*)).

Global Instance Method_Box_new `{State.Trait} {A : Set} :
  Notation.DoubleColon Box "new" := {
  Notation.double_colon (x : A) := new x;
}.
