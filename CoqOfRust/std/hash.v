Require Import CoqOfRust.lib.lib.

Module random.
  (* pub struct RandomState { /* private fields */ } *)
  Module RandomState.
    Parameter t : Set.
  End RandomState.

  (* pub struct DefaultHasher(/* private fields */); *)
  Module DefaultHasher.
    Parameter t : Set.
  End DefaultHasher.
End random.
