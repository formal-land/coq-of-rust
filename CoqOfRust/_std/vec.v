Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust._std.alloc.
(* Require Import CoqOfRust._std.iter. *)
Require Import CoqOfRust._std.ops.

(* ********STRUCTS******** *)
(* 
[?] DrainFilter
[?] Drain
[?] IntoIter
[?] Splice
[?] Vec
*)

(* BUGGED: defaultType + where clause *)
(* BUGGED: monad function dependency *)
(* Do we make a match clause in the definition to resolve this issue? *)
(* 
pub struct DrainFilter<'a, T, F, A = Global>
where
    A: Allocator,
    F: FnMut(&mut T) -> bool,
{ /* private fields */ }
*)
Module DrainFilter.
  Record t (T F A : Set) : Set := { }.
End DrainFilter.
Definition DrainFilter (T F : Set) (A : option Set)
  `{Allocator.Trait (defaultType A Global)} 
  `{FnMut.Trait F (mut_ref T -> bool)}
  : Set :=
  DrainFilter.t T F (defaultType A Global).
  (* 
  let A_type := (defaultType A Global) in
  let traits 
    `{Allocator.Trait A_type} 
    := unit in
    DrainFilter.t T F A_type. *)

(* BUGGED: same as above *)
(* 
pub struct Drain<'a, T, A = Global>
where
    T: 'a,
    A: Allocator + 'a,
{ /* private fields */ }
*)
Module Drain.
  Record t (T A: Set) : Set := { }.
End Drain.
Definition Drain (T : Set) (A : option Set) : Set :=
  Drain.t T (defaultType A Global).
  (* 
  let A_type := (defaultType A Global) in
  let traits 
    `{Allocator.Trait A_type} 
    := unit in
    Drain.t T A_type. *)

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
  (* 
  let A_type := (defaultType A Global) in
  let traits 
    `{Allocator.Trait A_type} 
    := unit in
    IntoIter.t T A_type. *)

(* BUGGED: same as above *)
(* BUGGED: Iterator dependency *)
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

  (* 
  let A_type := (defaultType A Global) in
  let traits 
    `{Allocator.Trait A_type} 
    := unit in
    Vec.t T A_type. *)
