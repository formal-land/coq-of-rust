(* To avoid circular dependency
 * implementations of external traits are defined in result_impl.v
 * This file contains only definitions of types.
 *)
Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(*
[x] IntoIter	
[x] Iter	
[x] IterMut	
*)
(* pub struct IntoIter<T> *)
Module IntoIter.
  Parameter t : Set -> Set.
End IntoIter.
Definition IntoIter := IntoIter.t.

(* 
pub struct Iter<'a, T>
where
    T: 'a, 
*)
Module Iter.
  Parameter t : Set -> Set.
End Iter.
Definition Iter := Iter.t.

(* 
pub struct IterMut<'a, T>
where
    T: 'a,
{ /* private fields */ }
*)
Module IterMut.
  Parameter t : Set -> Set.
End IterMut.
Definition IterMut := IterMut.t.

(* ********ENUMS******** *)
(* 
[x] Result
*)

Module Result.
  Inductive t (T E : Set) : Set :=
  | Ok : T -> t T E
  | Err : E -> t T E.
  Arguments Ok {T E} _.
  Arguments Err {T E} _.
End Result.
Definition Result `{State.Trait} (T E : Set) : Set :=
  M.Val (Result.t T E).
