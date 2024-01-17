Require Import CoqOfRust.lib.lib.

Module  Impl.
Section Impl.
  Context {T : Set}.

  Definition Self : Set := slice T.

  (*
  pub fn sort(&mut self)
  where
      T: Ord,
  *)
  Parameter sort : mut_ref Self -> M unit.

  Global Instance AF_sort :
    Notations.DoubleColon Self "sort" := {|
    Notations.double_colon := sort;
  |}.
End Impl.
End Impl.
