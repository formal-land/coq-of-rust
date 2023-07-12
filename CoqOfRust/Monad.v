(* Imports monad-related definitions *)
Require StateMonad.

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

(** Provide definitions of control flow statements
  * (A := unit) because they retrun nothing
  *)
Definition Break `{StateMonad.State.Trait} : M unit := StateMonad.Break.
Definition Continue `{StateMonad.State.Trait} : M unit := StateMonad.Continue.
Definition loop `{StateMonad.State.Trait} (* {A : Set} *) : M unit -> M unit :=
  StateMonad.loop.

Module Notations.
  Notation "'let*' a := b 'in' c" :=
    (bind b (fun a => c))
      (at level 200, b at level 100, a name).
End Notations.

Module State := StateMonad.State.
