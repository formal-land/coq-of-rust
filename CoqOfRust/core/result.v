(* To avoid circular dependency
 * the translation of core::result.rs is split into two files
 *)

Require Export CoqOfRust.core.result_types.
Require Export CoqOfRust.core.result_impl.

Module IntoIter := IntoIter.
Module Iter := Iter.
Module IterMut := IterMut.
Module Result := Result.
Module Impl_PartialEq_for_Result := Impl_PartialEq_for_Result.

Definition IntoIter := IntoIter.t.
Definition Iter := Iter.t.
Definition IterMut := IterMut.t.
Definition Result := Result.t.
