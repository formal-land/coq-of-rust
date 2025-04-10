Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.borrow.

(*
pub trait Borrow<Borrowed>
where
    Borrowed: ?Sized,
{
    // Required method
    fn borrow(&self) -> &Borrowed;
}
*)
Module Borrow.
  Definition trait (Self Borrowed : Set) `{Link Self} `{Link Borrowed} : TraitMethod.Header.t :=
    ("core::borrow::Borrow", [], [ Φ Borrowed ], Φ Self).

  Definition Run_borrow (Self Borrowed : Set) `{Link Self} `{Link Borrowed} : Set :=
    TraitMethod.C (trait Self Borrowed) "borrow" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] (Ref.t Pointer.Kind.Ref Borrowed)).

  Class Run (Self Borrowed : Set) `{Link Self} `{Link Borrowed} : Set := {
    borrow : Run_borrow Self Borrowed;
  }.
End Borrow.

(* impl<T: ?Sized> Borrow<T> for T *)
Module Impl_Borrow_T_for_T.
  Definition Self (T : Set): Set :=
    T.

  Instance run (T : Set) `{Link T} : Borrow.Run (Self T) T.
  Admitted.
End Impl_Borrow_T_for_T.
Export Impl_Borrow_T_for_T.
