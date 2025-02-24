Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import core.clone.

Import Run.

(*
    pub trait Clone: Sized {
        fn clone(&self) -> Self;

        fn clone_from(&mut self, source: &Self) {
            *self = source.clone()
        }
    }
*)
Module Clone.
  Definition Run_clone (Self : Set) `{Link Self} : Set :=
    {clone @
      IsTraitMethod.t "core::clone::Clone" (Φ Self) [] "clone" clone *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ clone [] [] [ φ self ] 🔽 Self }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
    clone : Run_clone Self;
    (* TODO: add [clone_from] *)
  }.
End Clone.

Module Impl_Clone_for_u64.
  Definition run_clone : clone.Clone.Run_clone U64.t.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Defined.
      { apply clone.impls.Impl_core_clone_Clone_for_u64.Implements. }
      { reflexivity. }
    }
    { intros.
      run_symbolic.
    }
  Defined.


  Definition run : clone.Clone.Run U64.t.
  Proof.
    constructor.
    { (* clone *)
      exact run_clone.
    }
  Defined.
End Impl_Clone_for_u64.
