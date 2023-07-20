Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(*
[x] IntoIter
[x] Iter
[x] IterMut
*)

(* pub struct IntoIter<A> { /* private fields */ } *)
Module IntoIter.
  Parameter t : Set -> Set.
End IntoIter.
Definition IntoIter := IntoIter.t.

(*
pub struct Iter<'a, A>
where
    A: 'a,
{ /* private fields */ }
*)
Module Iter.
  Parameter t : Set -> Set.
End Iter.
Definition Iter := Iter.t.

(* pub struct IterMut<'a, A>
where
    A: 'a,
{ /* private fields */ } *)
Module IterMut.
  Parameter t : Set -> Set.
End IterMut.
Definition IterMut := IterMut.t.


(* ********ENUMS******** *)
(*
[x] Option
*)

Module Option.
  Inductive t (T : Set) : Set :=
  | None : t T
  | Some : T -> t T.
  Arguments None {_}.
  Arguments Some {_}.
End Option.
Definition Option := Option.t.
