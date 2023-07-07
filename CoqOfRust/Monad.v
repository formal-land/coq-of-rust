(* Imports monad-related definitions *)
Require experiments.StateMonad.

(* Parameter State Address : Set.
Instance H : StateMonad.State.Trait State Address. Admitted. *)

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

Module Notations.
  Notation "'let*' a := b 'in' c" :=
    (bind b (fun a => c))
      (at level 200, b at level 100, a name).
End Notations.
