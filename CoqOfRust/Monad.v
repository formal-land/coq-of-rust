(* Imports monad-related definitions *)
Require Export StateMonad.

(** A sketch of the [M] monad *)
Definition M `{StateMonad.State.Trait} := StateMonad.M : Set -> Set.
Definition Pure
  `{StateMonad.State.Trait} {a : Set} :=
  StateMonad.pure : a -> M a.
Definition bind
  `{StateMonad.State.Trait} {a b : Set} :=
  StateMonad.bind : M a -> (a -> M b) -> M b.

(** Used for the definitions of "const". *)
Parameter run : forall `{StateMonad.State.Trait} {A : Set}, M A -> A.

(** Provide definitions of control flow statements *)
Definition Break `{State.Trait} {A : Set} : M A := StateMonad.Break.
Definition Continue `{State.Trait} {A : Set} : M A := StateMonad.Continue.

Module Notations.
  Notation "'let*' a := b 'in' c" :=
    (bind b (fun a => c))
      (at level 200, b at level 100, a name).
End Notations.
