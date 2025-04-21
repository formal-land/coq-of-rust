Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.option.
Require Import core.ops.links.index.
Require Import core.ops.links.range.

(*
  pub unsafe trait SliceIndex<T: ?Sized>: private_slice_index::Sealed {
    type Output: ?Sized;
    fn get(self, slice: &T) -> Option<&Self::Output>;
    fn get_mut(self, slice: &mut T) -> Option<&mut Self::Output>;
    unsafe fn get_unchecked(self, slice: *const T) -> *const Self::Output;
    unsafe fn get_unchecked_mut(self, slice: *mut T) -> *mut Self::Output;
    fn index(self, slice: &T) -> &Self::Output;
    fn index_mut(self, slice: &mut T) -> &mut Self::Output;
  }
*)
Module SliceIndex.
  Definition run_get 
      (Self : Set) `{Link Self} 
      (T : Set) `{Link T} 
      (Output : Set) `{Link Output} : Set :=
    { get @ 
      IsTraitMethod.t "core::slice::index::SliceIndex" [] [Φ T] (Φ Self) "get" get *
      forall (self : Self) (slice : Ref.t Pointer.Kind.Ref T),
        {{ get [] [] [ φ self; φ slice ] 🔽 
        option (Ref.t Pointer.Kind.Ref Output) }}
    }.

  Definition run_get_mut 
      (Self : Set) `{Link Self} 
      (T : Set) `{Link T} 
      (Output : Set) `{Link Output} : Set :=
    { get_mut @ 
      IsTraitMethod.t "core::slice::index::SliceIndex" [] [Φ T] (Φ Self) "get_mut" get_mut *
      forall (self : Self) (slice : Ref.t Pointer.Kind.MutRef T),
        {{ get_mut [] [] [ φ self; φ slice ] 🔽 
        option (Ref.t Pointer.Kind.MutRef Output) }}
    }.

  Definition run_get_unchecked 
      (Self : Set) `{Link Self} 
      (T : Set) `{Link T} 
      (Output : Set) `{Link Output} : Set :=
    { get_unchecked @ 
      IsTraitMethod.t "core::slice::index::SliceIndex" [] [Φ T] (Φ Self) "get_unchecked" get_unchecked *
      forall (self : Self) (slice : Ref.t Pointer.Kind.ConstPointer T),
        {{ get_unchecked [] [] [ φ self; φ slice ] 🔽 
        Ref.t Pointer.Kind.ConstPointer Output }}
    }.

  Definition run_get_unchecked_mut 
      (Self : Set) `{Link Self} 
      (T : Set) `{Link T} 
      (Output : Set) `{Link Output} : Set :=
    { get_unchecked_mut @ 
      IsTraitMethod.t "core::slice::index::SliceIndex" [] [Φ T] (Φ Self) "get_unchecked_mut" get_unchecked_mut *
      forall (self : Self) (slice : Ref.t Pointer.Kind.Ref T),
        {{ get_unchecked_mut [] [] [ φ self; φ slice ] 🔽 
        Ref.t Pointer.Kind.Ref Output }}
    }.

  Definition run_index 
      (Self : Set) `{Link Self}
      (T : Set) `{Link T}
      (Output : Set) `{Link Output} :
      Set := 
    { index @ 
      IsTraitMethod.t "core::slice::index::SliceIndex" [] [Φ T] (Φ Self) "index" index *
      forall (self : Self) (slice : Ref.t Pointer.Kind.Ref T),
        {{ index [] [] [ φ self; φ slice ] 🔽 
        Ref.t Pointer.Kind.Ref Output }}
    }.

  Definition run_index_mut 
      (Self : Set) `{Link Self}
      (T : Set) `{Link T}
      (Output : Set) `{Link Output} :
      Set := 
    { index_mut @ 
      IsTraitMethod.t "core::slice::index::SliceIndex" [] [Φ T] (Φ Self) "index_mut" index_mut *
      forall (self : Self) (slice : Ref.t Pointer.Kind.MutRef T),
        {{ index_mut [] [] [ φ self; φ slice ] 🔽 
        Ref.t Pointer.Kind.MutRef Output }}
    }.

  Class Run
      (Self : Set) `{Link Self}
      (T : Set) `{Link T}
      (Output : Set) `{Link Output} :
    Set := {
      Output_IsAssociated :
        IsTraitAssociatedType
          "core::slice::index::SliceIndex" [] [Φ T] (Φ Self)
          "Output" (Φ Output);
      get : run_get Self T Output;
      get_mut : run_get_mut Self T Output;
      get_unchecked : run_get_unchecked Self T Output;
      get_unchecked_mut : run_get_unchecked_mut Self T Output;
      index : run_index Self T Output;
      index_mut : run_index_mut Self T Output;
  }.
End SliceIndex.

(* unsafe impl<T> SliceIndex<[T]> for usize {
    type Output = T; *)
Module Impl_SliceIndex_for_Usize.
  Instance run
    (T : Set) `{Link T} :
    SliceIndex.Run Usize.t (list T) T.
  Admitted.
End Impl_SliceIndex_for_Usize.
Export Impl_SliceIndex_for_Usize.

(*
impl<T, I> ops::IndexMut<I> for [T]
where
    I: SliceIndex<[T]>,
*)
Module Impl_IndexMut_for_Slice.
  Definition Self (T I : Set) : Set :=
    list T.

  Instance run
    (T I : Set) `{Link T} `{Link I}
    {Index_Output : Set} `{Link Index_Output}
    (run_SliceIndex_for_I : SliceIndex.Run I (list T) Index_Output) :
    IndexMut.Run (Self T I) I Index_Output.
  Admitted.
End Impl_IndexMut_for_Slice.
Export Impl_IndexMut_for_Slice.

(* unsafe impl<T> SliceIndex<[T]> for ops::RangeTo<usize> *)
Module Impl_SliceIndex_for_RangeTo.
  Definition Self (T : Set) : Set :=
    RangeTo.t Usize.t.

  (* type Output = [T]; *)
  Definition Output (T : Set) : Set :=
    list T.

  Instance run
    (T : Set) `{Link T} :
    SliceIndex.Run (Self T) (list T) (Output T).
  Admitted.
End Impl_SliceIndex_for_RangeTo.
Export Impl_SliceIndex_for_RangeTo.
