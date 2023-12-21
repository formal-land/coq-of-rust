Require Import CoqOfRust.lib.lib.

Require CoqOfRust.core.default.

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

(*
pub struct Iter<'a, A>
where
    A: 'a,
{ /* private fields */ }
*)
Module Iter.
  Parameter t : Set -> Set.
End Iter.

(* pub struct IterMut<'a, A>
where
    A: 'a,
{ /* private fields */ } *)
Module IterMut.
  Parameter t : Set -> Set.
End IterMut.


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

Module Impl_Option. Section Impl_Option.
  Context {T : Set}.

  Definition Self : Set := Option.t T.

  Definition unwrap_or_default {H0 : core.default.Default.Trait T}
      (self : Self) : M T :=
    match self with
    | Option.None => core.default.Default.default (Self := T)
    | Option.Some x => M.pure x
    end.

  Global Instance AF_unwrap_or_default {H0 : core.default.Default.Trait T} :
    Notations.DoubleColon Self "unwrap_or_default" := {
    Notations.double_colon := unwrap_or_default;
  }.

  Definition unwrap_or (self : Self) (default : T) : M T :=
    match self with
    | Option.None => M.pure default
    | Option.Some x => M.pure x
    end.

  Global Instance AF_unwrap_or : Notations.DoubleColon Self "unwrap_or" := {
    Notations.double_colon := unwrap_or;
  }.

  Global Instance I_Default {ℋ : default.Default.Trait T} :
    default.Default.Trait (core.option.Option.t T).
  Admitted.

  Global Instance I_Clone {ℋ : clone.Clone.Trait T} :
    clone.Clone.Trait (core.option.Option.t T).
  Admitted.
End Impl_Option. End Impl_Option.
