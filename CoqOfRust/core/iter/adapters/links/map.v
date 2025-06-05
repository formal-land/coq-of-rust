Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.iter.traits.links.iterator.

Require Export core.iter.adapters.links.map_Map.

(*
impl<B, I: Iterator, F> Iterator for Map<I, F>
  where
      F: FnMut(I::Item) -> B,
*)
Module Impl_Iterator_for_Map.
  Definition Self (I F : Set) : Set :=
    Map.t I F.

  Instance run (B I F : Set) `{Link B} `{Link I} `{Link F} :
    Iterator.Run (Self I F) B.
  Admitted.
End Impl_Iterator_for_Map.
Export Impl_Iterator_for_Map.
