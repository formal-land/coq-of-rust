(* Imports monad-related definitions *)
Require MonadExperiments.

(** A sketch of the [M] monad *)
Definition M := MonadExperiments.M : Set -> Set.
Definition Pure :=
  (fun _ => MonadExperiments.pure) : forall {a : Set}, a -> M a.
Definition bind :=
  (fun _ _ => MonadExperiments.bind) :
  forall {a b : Set}, M a -> (a -> M b) -> M b.

(** Used for the definitions of "const". *)
Parameter run : forall {A : Set}, M A -> A.

Module Notations.
  Notation "'let*' a := b 'in' c" :=
    (bind b (fun a => c))
      (at level 200, b at level 100, a name).
End Notations.
