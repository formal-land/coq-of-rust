Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.slice.mod.
Require Import core.slice.links.index.
Require Import core.slice.links.iter.
Require core.links.option.

Module Impl_Slice.
  Definition Self (T : Set) `{Link T} : Set := list T.
  
  (*
    pub fn get<I>(&self, index: I) -> Option<&I::Output>
    where
        I: SliceIndex<Self>,
  *)
  Instance run_get
      (T : Set) `{Link T}
      {I : Set} `{Link I} 
      {Output : Set} `{Link Output}
      (run_SliceIndex_for_I : SliceIndex.Run I (T := Self T) (Output := Output))
      (self : Ref.t Pointer.Kind.Ref (Self T)) 
      (index : I) :
    Run.Trait (slice.Impl_slice_T.get (Φ T)) [] [Φ I] [φ self; φ index]
      (option (Ref.t Pointer.Kind.Ref Output)).
  Admitted.

  (*
    pub unsafe fn get_unchecked_mut<I>(&mut self, index: I) -> &mut I::Output
        where
            I: SliceIndex<Self>,
  *)
  Instance run_get_unchecked_mut 
      (T : Set) `{Link T}
      {I : Set} `{Link I} 
      {Output : Set} `{Link Output}
      (run_SliceIndex_for_I : SliceIndex.Run I (T := Self T) (Output := Output))
      (self : Ref.t Pointer.Kind.MutRef (Self T)) 
      (index : I) :
    Run.Trait (slice.Impl_slice_T.get_unchecked_mut (Φ T)) [] [Φ I] [φ self; φ index]
      (Ref.t Pointer.Kind.MutRef Output).
  Admitted.

  (* pub const fn len(&self) -> usize *)
  Instance run_len
      (T : Set) `{Link T}
      (self : Ref.t Pointer.Kind.Ref (Self T)) :
    Run.Trait (slice.Impl_slice_T.len (Φ T)) [] [] [φ self]
      Usize.t.
  Admitted.

  (* pub fn iter_mut(&mut self) -> IterMut<'_, T> *)
  Instance run_iter_mut
      (T : Set) `{Link T}
      (self : Ref.t Pointer.Kind.MutRef (Self T)) :
    Run.Trait (slice.Impl_slice_T.iter_mut (Φ T)) [] [] [φ self]
      (IterMut.t T).
  Admitted.
End Impl_Slice.
