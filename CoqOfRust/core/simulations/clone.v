Require Import CoqOfRust.CoqOfRust.
Require Import proofs.M.
Require Import simulations.M.

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
  Record RunImpl `{State.Trait} (Self : Set) `{ToTy Self} `{ToValue Self} : Set := {
    clone : {clone @
      IsTraitMethod.t "core::clone::Clone" (Φ Self) [] "clone" clone *
      forall (state : State) (pointer : Pointer.t Value.t),
        HasRead.t state pointer φ ->
        {{ _, state |
          clone [] [ Value.Pointer pointer ] ⇓
          fun (v : Self) => inl (φ v)
        | fun state' => state' = state }}
    };
    (* TODO: add [clone_from] *)
  }.
End Clone.
