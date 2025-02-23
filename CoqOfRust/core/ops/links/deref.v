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
