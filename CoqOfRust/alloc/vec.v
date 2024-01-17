Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.core.alloc.
Require Import CoqOfRust.core.cmp.
(* Require Import CoqOfRust.std.iter. *)
Require Import CoqOfRust.std.ops.

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

    Module Default.
      Definition A : Set := alloc.Global.t.
    End Default.
  End IntoIter.
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

  Global Instance AF_new :
    Notations.DoubleColon Self "new" := {
    Notations.double_colon := new;
  }.

  Parameter push : mut_ref Self -> T -> M unit.

  Global Instance AF_push :
    Notations.DoubleColon Self "push" := {
    Notations.double_colon := push;
  }.

  (* pub fn dedup(&mut self) *)
  Parameter dedup :
    forall {H0 : core.cmp.PartialEq.Trait T (Rhs := T)},
    mut_ref Self -> M unit.

  Global Instance AF_dedup {H0 : core.cmp.PartialEq.Trait T} :
    Notations.DoubleColon Self "dedup" := {
    Notations.double_colon := dedup (H0 := H0);
  }.

  (* pub fn len(&self) -> usize *)
  Parameter len : ref Self -> M usize.t.

  Global Instance AF_len :
    Notations.DoubleColon Self "len" := {
    Notations.double_colon := len;
  }.

  (* pub fn swap_remove(&mut self, index: usize) -> T *)
  Parameter swap_remove :
    mut_ref Self -> usize.t -> M T.

  Global Instance AF_swap_remove :
    Notations.DoubleColon Self "swap_remove" := {
    Notations.double_colon := swap_remove;
  }.

  (* pub fn is_empty(&self) -> bool *)
  Parameter is_empty : ref Self -> M bool.t.

  Global Instance AF_is_empty :
    Notations.DoubleColon Self "is_empty" := {
    Notations.double_colon := is_empty;
  }.

  (* pub fn as_ptr(&self) -> *const T *)
  Parameter as_ptr : ref Self -> M (ref T).

  Global Instance AF_as_ptr :
    Notations.DoubleColon Self "as_ptr" := {
    Notations.double_colon := as_ptr;
  }.

  (* pub fn as_slice(&self) -> &[T] *)
  Parameter as_slice : ref Self -> M (ref (slice T)).

  Global Instance AF_as_slice :
    Notations.DoubleColon Self "as_slice" := {
    Notations.double_colon := as_slice;
  }.

  (* pub fn with_capacity(capacity: usize) -> Vec<T> *)
  Parameter with_capacity : usize.t -> M (Vec.t T Vec.Default.A).

  Global Instance AF_with_capacity :
    Notations.DoubleColon Self "with_capacity" := {
    Notations.double_colon := with_capacity;
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
