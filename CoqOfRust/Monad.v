(* Imports monad-related definitions *)
Require StateMonad.

Module State := StateMonad.State.

(** A sketch of the [M] monad *)
Definition M `{State.Trait} := StateMonad.M : Set -> Set.
Definition Pure
  `{State.Trait} {a : Set} :=
  StateMonad.pure : a -> M a.
Definition bind
  `{State.Trait} {a b : Set} :=
  StateMonad.bind : M a -> (a -> M b) -> M b.

(** Used for the definitions of "const". *)
Parameter run : forall `{State.Trait} {A : Set}, M A -> A.

(** Provide definitions of control flow statements
  * (A := unit) because they retrun nothing
  *)
Definition Break `{State.Trait} : M unit := StateMonad.Break.
Definition Continue `{State.Trait} : M unit := StateMonad.Continue.
Definition loop `{State.Trait} (* {A : Set} *) : M unit -> M unit :=
  StateMonad.loop.

Definition val (A : Set) `{State.Trait} : Set := StateMonad.Ref A.

Module Notations.
  Notation "'let*' a := b 'in' c" :=
    (bind b (fun a => c))
      (at level 200, b at level 100, a name).

  Notation "⟅ e ⟆" := (val e) (at level 0).
End Notations.
