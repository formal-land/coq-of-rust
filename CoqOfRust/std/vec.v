Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.std.alloc.
(* Require Import CoqOfRust.std.iter. *)

(* ********STRUCTS******** *)
(* 
[?] DrainFilter
[?] Drain
[?] IntoIter
[?] Splice
[?] Vec
*)

(* BUGGED: defaultType + where clause *)
(* 
pub struct DrainFilter<'a, T, F, A = Global>
where
    A: Allocator,
    F: FnMut(&mut T) -> bool,
{ /* private fields */ }
*)
Module DrainFilter.
  Record t (T F A): Set := { }.
End DrainFilter.
Definition DrainFilter (T F : Set) (A : option Set) := DrainFilter.t T F (defaultType A Global).

(* BUGGED: same as above *)
(* 
pub struct Drain<'a, T, A = Global>
where
    T: 'a,
    A: Allocator + 'a,
{ /* private fields */ }
*)
Module Drain.
  Record t (T A) : Set := { }.
End Drain.
Definition Drain (T : Set) (A : option Set) := Drain.t T (defaultType A Global).

(* BUGGED: same as above *)
(* 
pub struct IntoIter<T, A = Global>
where
    A: Allocator,
{ /* private fields */ }
*)
Module IntoIter.
  Record t (T A : Set) : Set := { }.
End IntoIter.
Definition IntoIter (T : Set) (A : option Set) := IntoIter.t T (defaultType A Global).

(* BUGGED: same as above *)
(* 
pub struct Splice<'a, I, A = Global>
where
    I: Iterator + 'a,
    A: Allocator + 'a,
{ /* private fields */ }
*)
Module Splice.
  Record t (I A : Set) : Set := { }.
End Splice.
Definition Splice (I : Set) (A : option Set) := Splice.t I (defaultType A Global).

(* BUGGED: same as above *)
(* 
pub struct Vec<T, A = Global>
where
    A: Allocator,
{ /* private fields */ }
*)
Module Vec.
  Record t (T A : Set): Set := { }.
End Vec.
Definition Vec (T : Set) (A : option Set) := Vec.t T (defaultType A Global).
