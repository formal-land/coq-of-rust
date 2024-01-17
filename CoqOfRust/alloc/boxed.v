Require Import CoqOfRust.lib.lib.

Require Import CoqOfRust.alloc.alloc.

(* ********STRUCTS******** *)
(* 
  [x] Box
*)
(* 
pub struct Box<T, A = Global>(_, _)
where
         A: Allocator,
         T: ?Sized;
*)
Module Box.
  Definition t (T A : Set) : Set := M.Ref T.

  Module Default.
    Definition A : Set := alloc.Global.t.
  End Default.

  Module  Impl.
  Section Impl.
    Context {T : Set}.

    Definition Self : Set := Box.t T alloc.Global.t.

    Parameter new :
      T -> M (Box.t T alloc.Global.t).

    Global Instance Method_Box_new :
        Notations.DoubleColon Self "new" := {
      Notations.double_colon := new;
    }.
  End Impl.
  End Impl.
End Box.
