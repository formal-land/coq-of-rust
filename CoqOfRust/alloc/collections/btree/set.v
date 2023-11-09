Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.alloc.
Require CoqOfRust.core.clone.

(* 
pub struct BTreeSet<K, A = Global>
where
    A: Allocator + Clone,
{ /* private fields */ }
*)
Module BTreeSet.
  Parameter t : forall (K A : Set)
    {H0 : alloc.Allocator.Trait A}
    {H1 : core.clone.Clone.Trait A},
    Set.

  Module Default.
    Definition A : Set := alloc.Global.
  End Default.
End BTreeSet.
Definition BTreeSet (K A : Set)
  {H0 : alloc.Allocator.Trait A}
  {H1 : core.clone.Clone.Trait A} :
  Set :=
  M.Val (BTreeSet.t K A).
