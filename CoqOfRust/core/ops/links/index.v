Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

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