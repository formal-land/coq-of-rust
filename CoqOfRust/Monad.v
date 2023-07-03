(** A sketch of the [M] monad *)
Parameter M : Set -> Set.
Parameter Pure : forall {a : Set}, a -> M a.
Parameter bind : forall {a b : Set}, M a -> (a -> M b) -> M b.

(** Used for the definitions of "const". *)
Parameter run : forall {A : Set}, M A -> A.

Module Notations.
  Notation "'let*' a := b 'in' c" :=
    (bind b (fun a => c))
      (at level 200, b at level 100, a name).
End Notations.

