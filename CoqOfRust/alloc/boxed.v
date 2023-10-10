Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.alloc.
Require Import CoqOfRust.core.fmt.

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
    Definition A : Set := core.alloc.Global.
  End Default.
End Box.
Definition Box (T : Set) (*(A : option Set)
  `{Allocator.Trait (defaultType A Global)}*)
  := Box.t T (*(defaultType A Global)*).

Parameter new :
  forall `{State.Trait} {T : Set},
  T -> M (Box T core.alloc.Global).

Global Instance Method_Box_new `{State.Trait} {T : Set} :
  Notation.DoubleColon (Box T core.alloc.Global) "new" := {
  Notation.double_colon (x : T) := new x;
}.

Global Instance Debug_for_Box `{State.Trait} {T A : Set} `{Debug.Trait T} :
  Debug.Trait (Box T A).
Admitted.
