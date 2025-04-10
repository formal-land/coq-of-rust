Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.array.
Require Import core.ops.links.index.

(*
impl<T, I, const N: usize> IndexMut<I> for [T; N]
where
    [T]: IndexMut<I>,
*)
Module Impl_IndexMut_for_Array.
  Definition Self (T I : Set) (N : Usize.t) : Set :=
    array.t T N.

  Instance run (T I : Set) `{Link T} `{Link I} (N : Usize.t)
    (IndexMut_Output : Set) `{Link IndexMut_Output}
    (run_IndexMut_for_slice_T : IndexMut.Run (list T) I IndexMut_Output) :
    IndexMut.Run (Self T I N) I IndexMut_Output.
  Admitted.
End Impl_IndexMut_for_Array.
Export Impl_IndexMut_for_Array.
