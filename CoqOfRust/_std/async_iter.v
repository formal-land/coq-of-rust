Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.core.option.
Require Import CoqOfRust._std.pin.
Require Import CoqOfRust._std.task.


(* ********STRUCTS******** *)
(* 
[x] FromIter
*)

(* pub struct FromIter<I> { /* private fields */ } *)
Module FromIter.
  Parameter t : Set -> Set.
End FromIter.
Definition FromIter := FromIter.t.


(* ********TRAITS******** *)
(* 
[x] AsyncIterator
*)
(* 
pub trait AsyncIterator {
    type Item;

    // Required method
    fn poll_next(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>
    ) -> Poll<Option<Self::Item>>;

    // Provided method
    fn size_hint(&self) -> (usize, Option<usize>) { ... }
}
*)
Module AsyncIterator.
  Class Trait `{State.Trait} (Self Item : Set) : Set := { 
    Item := Item;

    poll_next : Pin (mut_ref Self) -> mut_ref Context -> Poll (Option Item);
    size_hint : ref Self -> usize * Option usize;
  }.
End AsyncIterator.


(* ********FUNCTIONS******** *)
(* 
[ ] from_iter
*)