Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(* 
[x] IntoIter
[x] TryFromSliceError
*)

(* pub struct IntoIter<T, const N: usize> *)
Module IntoIter.
  Record t (T : Set) (N : usize): Set := { }.
End IntoIter. 
Definition IntoIter := IntoIter.t.


(* pub struct TryFromSliceError(_); *)
Module TryFromSliceError.
  Record t (underscore : Set) : Set := { }.
End TryFromSliceError.
Definition TryFromSliceError := TryFromSliceError.t.
