Require Import CoqOfRust.lib.lib.

(* ********STRUCTS******** *)
(* 
[x] IntoIter
[x] TryFromSliceError
*)

(* pub struct IntoIter<T, const N: usize> *)
Module IntoIter.
  Parameter t : Set -> Set.
End IntoIter.


(* pub struct TryFromSliceError(_); *)
Module TryFromSliceError.
  Parameter t : Set.
End TryFromSliceError.
