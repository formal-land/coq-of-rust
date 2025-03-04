Require Import CoqOfRust.CoqOfRust.
Require Import links.M.

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
      IsTraitMethod.t "core::clone::Clone" [] [] (Φ Self) "clone" clone *
      forall (self : Ref.t Pointer.Kind.Ref Self),
        {{ clone [] [] [ φ self ] 🔽 Self }}
    }.

  Record Run (Self : Set) `{Link Self} : Set := {
    clone : Run_clone Self;
    (* TODO: add [clone_from] *)
  }.
End Clone.
