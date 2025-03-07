Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

(*
  pub trait Index<Idx: ?Sized> {
    type Output: ?Sized;

    fn index(&self, index: Idx) -> &Self::Output;
  }
*)
Module Index.
  Definition run_index 
      (Self : Set) `{Link Self} 
      (Idx : Set) `{Link Idx} 
      (Output : Set) `{Link Output} : Set :=
    { index' @ 
      IsTraitMethod.t "core::ops::index::Index" [] [Φ Idx] (Φ Self) "index" index' *
      forall (self : Ref.t Pointer.Kind.Ref Self) (index : Idx),
        {{ index' [] [] [φ self; φ index] 🔽 Ref.t Pointer.Kind.Ref Output }}
    }.

  Record Run
      (Self : Set) `{Link Self}
      {Idx : Set} `{Link Idx}
      {Output : Set} `{Link Output} : 
    Set := {
      Output_IsAssociated :
      IsTraitAssociatedType
        "core::slice::index::SliceIndex" [] [Φ Idx] (Φ Self)
        "Output" (Φ Output);
      index : run_index Self Idx Output;
  }.
End Index.