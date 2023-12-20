Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.alloc.alloc.

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
  Definition t (T A : Set) : Set := T.

  Module Default.
    Definition A : Set := alloc.Global.t.
  End Default.
End Box.
Definition Box (T : Set) (*(A : option Set)
  `{Allocator.Trait (defaultType A Global)}*)
  := Box.t T (*(defaultType A Global)*).

Parameter new :
  forall {T : Set},
  T -> M (Box T alloc.Global.t).

Global Instance Method_Box_new {T : Set} :
  Notations.DoubleColon (Box T alloc.Global.t) "new" := {
  Notations.double_colon (x : T) := new x;
}.
