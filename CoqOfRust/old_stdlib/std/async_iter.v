Require Import CoqOfRust.lib.lib.
Require Import CoqOfRust.core.option.
Require Import CoqOfRust.std.pin.
Require Import CoqOfRust.std.task.


(* ********STRUCTS******** *)
(* 
[x] FromIter
*)

(* pub struct FromIter<I> { /* private fields */ } *)
Module FromIter.
  Parameter t : Set -> Set.
End FromIter.


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
  Class Trait (Self Item : Set) : Set := { 
    Item := Item;

    poll_next :
      M.Val (Pin (mut_ref Self)) ->
      M.Val (mut_ref Context) ->
      M (M.Val (Poll (Option.t Item)));
    size_hint :
      M.Val (ref Self) ->
      M (M.Val (usize.t * Option.t usize.t));
  }.
End AsyncIterator.


(* ********FUNCTIONS******** *)
(* 
[ ] from_iter
*)