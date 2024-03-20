Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.alloc.

(* ********STRUCTS******** *)
(*
[x] Rc
[x] Weak
*)
(* 
pub struct Rc<T: ?Sized, A: Allocator = Global> { /* private fields */ }
*)
Module Rc.
  Parameter t : forall (T A : Set), Set.

  Module  Impl_T.
  Section Impl_T.
    Context {T : Set}.

    Definition Self : Set := t T alloc.Global.t.

    (* pub fn new(value: T) -> Rc<T> *)
    Parameter new : T -> M Self.

    Global Instance AF_new : Notations.DoubleColon Self "new" := {
      Notations.double_colon := new;
    }.
  End Impl_T.
  End Impl_T.

  Module  Impl_T_A.
  Section Impl_T_A.
    Context {T A : Set}.

    Definition Self : Set := t T A.

    (* pub fn strong_count(this: &Rc<T, A>) -> usize *)
    Parameter strong_count : ref (t T A) -> M usize.t.

    Global Instance AF_strong_count : Notations.DoubleColon Self "strong_count" := {
      Notations.double_colon := strong_count;
    }.
  End Impl_T_A.
  End Impl_T_A.
End Rc.

(* 
pub struct Weak<T>
where
    T: ?Sized,
{ /* private fields */ }
*)
Module Weak.
  Parameter t : forall (T : Set), Set.
End Weak.
