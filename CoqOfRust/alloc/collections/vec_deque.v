Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.alloc.
Require CoqOfRust.core.clone.

(* pub struct VecDeque<T, A: Allocator = Global> { /* private fields */ } *)
Module VecDeque.
  Parameter t : forall `{State.Trait} (T A : Set)
    {H0 : alloc.Allocator.Trait A},
    Set.

  Module Default.
    Definition A : Set := alloc.Global.
  End Default.
End VecDeque.
Definition VecDeque `{State.Trait} (T A : Set)
  {H0 : alloc.Allocator.Trait A} :
  Set :=
  M.Val (VecDeque.t T A).
