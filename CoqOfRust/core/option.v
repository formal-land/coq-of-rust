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
      (self : M.Val Self) : M (M.Val T) :=
    let* self := M.read self in
    match self with
    | Option.None => core.default.Default.default (Self := T)
    | Option.Some x => M.alloc x
    end.

  Global Instance AF_unwrap_or_default {H0 : core.default.Default.Trait T} :
    Notation.DoubleColon Self "unwrap_or_default" := {
    Notation.double_colon := unwrap_or_default;
  }.
End Impl_Option. End Impl_Option.
