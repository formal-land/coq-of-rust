Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.clone.

(*
    pub trait Clone: Sized {
        fn clone(&self) -> Self;
        fn clone_from(&mut self, source: &Self)
    }
*)
Module Clone.
  Definition trait (Self : Set) `{Link Self} : TraitMethod.Header.t :=
    ("core::clone::Clone", [], [], Φ Self).

  Definition Run_clone (Self : Set) `{Link Self} : Set :=
    TraitMethod.C (trait Self) "clone" (fun method =>
      forall (self : Ref.t Pointer.Kind.Ref Self),
      Run.Trait method [] [] [ φ self ] Self
    ).

  Class Run (Self : Set) `{Link Self} : Set := {
    clone : Run_clone Self;
    (* TODO: add [clone_from] *)
  }.
End Clone.

Module Impl_Clone_for_bool.
  Definition Self : Set :=
    bool.

  Definition run_clone : clone.Clone.Run_clone bool.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply clone.impls.Impl_core_clone_Clone_for_bool.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
    }
  Defined.


  Instance run : clone.Clone.Run bool := {
    Clone.clone := run_clone;
  }.
End Impl_Clone_for_bool.
