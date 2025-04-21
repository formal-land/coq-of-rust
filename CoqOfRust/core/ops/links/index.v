Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.links.array.
(*
  pub trait Index<Idx: ?Sized> {
    type Output: ?Sized;

    fn index(&self, index: Idx) -> &Self::Output;
  }
*)
Module Index.
  Definition trait (Self Idx : Set) `{Link Self} `{Link Idx} : TraitMethod.Header.t :=
    ("core::ops::index::Index", [], [Φ Idx], Φ Self).

  Definition Run_index
      (Self Idx Output : Set) `{Link Self} `{Link Idx} `{Link Output} :
      Set :=
    TraitMethod.C (trait Self Idx) "index" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self) (index : Idx),
      Run.Trait method [] [] [ φ self; φ index ] (Ref.t Pointer.Kind.Ref Output)
    ).

  Class Run
      (Self : Set) `{Link Self}
      (Idx : Set) `{Link Idx}
      (Output : Set) `{Link Output} : 
    Set := {
      Output_IsAssociated :
      IsTraitAssociatedType
        "core::slice::index::SliceIndex" [] [Φ Idx] (Φ Self)
        "Output" (Φ Output);
      index : Run_index Self Idx Output;
  }.
End Index.

(*
impl<T, I, const N: usize> Index<I> for [T; N]
where
    [T]: Index<I>,
*)
Module Impl_Index_for_Array.
  Definition Self (T I : Set) (N : Usize.t) : Set :=
    array.t T N.

  (* type Output = <[T] as Index<I>>::Output; *)
  Definition Output (T I : Set) (N : Usize.t) {Index_Output : Set}
      `{Link T} `{Link I} `{Link Index_Output}
      {run_Index_for_slice_T : Index.Run T I Index_Output} :
      Set :=
    Index_Output.

  Instance run (T I : Set) (N : Usize.t) {Index_Output : Set}
      `{Link T} `{Link I} `{Link Index_Output}
      {run_Index_for_slice_T : Index.Run T I Index_Output} :
    Index.Run (Self T I N) I (Output T I N).
  Admitted.
End Impl_Index_for_Array.

(*
pub trait IndexMut<Idx>: Index<Idx>
where
    Idx: ?Sized,
{
    // Required method
    fn index_mut(&mut self, index: Idx) -> &mut Self::Output;
}
*)
Module IndexMut.
  Definition trait (Self Idx : Set) `{Link Self} `{Link Idx} : TraitMethod.Header.t :=
    ("core::ops::index::IndexMut", [], [Φ Idx], Φ Self).

  Definition Run_index_mut
      (Self Idx Output : Set) `{Link Self} `{Link Idx} `{Link Output} :
      Set :=
    TraitMethod.C (trait Self Idx) "index_mut" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self) (index : Idx),
      Run.Trait method [] [] [ φ self; φ index ] (Ref.t Pointer.Kind.MutRef Output)
    ).

  Class Run
    (Self : Set) `{Link Self}
    (Idx : Set) `{Link Idx}
    (Output : Set) `{Link Output} :
    Set := {
      run_Index_for_Self : Index.Run Self Idx Output;
      index_mut : Run_index_mut Self Idx Output;
    }.
End IndexMut.
