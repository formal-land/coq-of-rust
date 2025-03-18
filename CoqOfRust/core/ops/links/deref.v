Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

Import Run.

(*
pub trait Deref {
    type Target: ?Sized;
    fn deref(&self) -> &Self::Target;
}
*)
Module Deref.
  Definition Run_deref
      (Self : Set) `{Link Self}
      {Target : Set} `{Link Target} :
      Set :=
    {deref @
      IsTraitMethod.t "core::ops::deref::Deref" [] [] (Φ Self) "deref" deref *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ deref [] [] [ φ self ] 🔽 Ref.t Pointer.Kind.Ref Target }}
    }.

  Record Run
      (Self : Set) `{Link Self}
      {Target : Set} `{Link Target} :
      Set := {
    deref : Run_deref Self (Target := Target);
  }.
End Deref.

(*
pub trait DerefMut: Deref {
    fn deref_mut(&mut self) -> &mut Self::Target;
}
*)
Module DerefMut.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("core::ops::deref::DerefMut", [], [], Φ Self).

  Definition Run_deref_mut
      (Self : Set) `{Link Self}
      (Target : Set) `{Link Target} :
      Set :=
    TraitMethod.C (trait Self) "deref_mut" (fun method =>
      forall (self : Ref.t Pointer.Kind.MutRef Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.MutRef Target)
    ).

  Class Run
      (Self : Set) `{Link Self}
      (Target : Set) `{Link Target} :
      Set := {
    deref_mut : Run_deref_mut Self Target;
  }.
End DerefMut.
