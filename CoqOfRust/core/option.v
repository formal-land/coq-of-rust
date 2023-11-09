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
Definition Option (T : Set) : Set :=
  M.Val (Option.t T).

Module Impl_Option. Section Impl_Option.
  Context {T : Set}.

  Definition Self : Set := Option T.

  Definition unwrap_or_default {H0 : core.default.Default.Trait T}
      (self : Self) : M T :=
    let* self := M.read self in
    match self with
    | Option.None => core.default.Default.default (Self := T)
    | Option.Some x => M.pure x
    end.

  Global Instance AF_unwrap_or_default {H0 : core.default.Default.Trait T} :
    Notation.DoubleColon Self "unwrap_or_default" := {
    Notation.double_colon := unwrap_or_default;
  }.
End Impl_Option. End Impl_Option.
