Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.alloc.
Require Import CoqOfRust.core.cmp.
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
  Parameter t : forall (T F A : Set), Set.
End DrainFilter.
Definition DrainFilter (T F : Set) (A : option Set)
  `{Allocator.Trait (defaultType A alloc.Global.t)} 
  `{FnMut.Trait F (mut_ref T -> bool)}
  : Set :=
  DrainFilter.t T F (defaultType A alloc.Global.t).
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
  Parameter t : forall (T A : Set), Set.
End Drain.
Definition Drain (T : Set) (A : option Set) : Set :=
  Drain.t T (defaultType A alloc.Global.t).
  (* 
  let A_type := (defaultType A Global) in
  let traits 
    `{Allocator.Trait A_type} 
    := unit in
    Drain.t T A_type. *)

(* BUGGED: same as above *)

Module into_iter.
  (* 
  pub struct IntoIter<T, A = Global>
  where
      A: Allocator,
  { /* private fields */ }
  *)
  Module IntoIter.
    Parameter t : forall (T A : Set), Set.
  End IntoIter.
  Definition IntoIter (T : Set) (A : option Set) :=
    IntoIter.t T (defaultType A alloc.Global.t).
    (* 
    let A_type := (defaultType A Global) in
    let traits 
      `{Allocator.Trait A_type} 
      := unit in
      IntoIter.t T A_type. *)

  (* BUGGED: same as above *)
  (* BUGGED: Iterator dependency *)
End into_iter.

(* 
pub struct Splice<'a, I, A = Global>
where
    I: Iterator + 'a,
    A: Allocator + 'a,
{ /* private fields */ }
*)
Module Splice.
  Parameter t : forall (I A : Set), Set.
End Splice.
Definition Splice (I : Set) (A : option Set) :=
  Splice.t I (defaultType A alloc.Global.t).

(* BUGGED: same as above *)
(* 
pub struct Vec<T, A = Global>
where
    A: Allocator,
{ /* private fields */ }
*)
Module Vec.
  Parameter t : forall (T A : Set), Set.

  Module Default.
    Definition A : Set := alloc.Global.t.
  End Default.
End Vec.
Definition Vec := Vec.t.

  (* 
  let A_type := (defaultType A Global) in
  let traits 
    `{Allocator.Trait A_type} 
    := unit in
    Vec.t T A_type. *)

Module Impl_Vec.
Section Impl_Vec.
  Context {T : Set}.

  Definition Self : Set := Vec T alloc.Global.t.

  Parameter new : M Self.

  Global Instance AssociatedFunction_new :
    Notations.DoubleColon Self "new" := {
    Notations.double_colon := new;
  }.

  Parameter push : Self -> T -> M unit.

  Global Instance Method_push :
    Notations.Dot "push" := {
    Notations.dot := push;
  }.

  Global Instance I_Default {ℋ_0 : default.Default.Trait T} :
    default.Default.Trait Self.
  Admitted.

  Global Instance I_PartialEq {U : Set}
      {ℋ_0 : cmp.PartialEq.Trait T (Rhs := U)} :
    cmp.PartialEq.Trait Self (Rhs := Vec.t U alloc.Global.t).
  Admitted.

  Global Instance I_Clone {ℋ_0 : clone.Clone.Trait T} :
    clone.Clone.Trait Self.
  Admitted.
End Impl_Vec.
End Impl_Vec.
