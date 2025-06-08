Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.ptr.const_ptr.

Module Impl_pointer_const_T.
  Definition Self (T : Set) `{Link T} : Set := Ref.t Pointer.Kind.ConstPointer T.

  (* pub const unsafe fn add(self, count: usize) -> Self *)
  Instance run_add
      (T : Set) `{Link T}
      (self : Self T)
      (count : Usize.t) :
    Run.Trait (ptr.const_ptr.Impl_pointer_const_T.add (Φ T)) [] [] [ φ self; φ count ] (Self T).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_pointer_const_T.
Export Impl_pointer_const_T.
