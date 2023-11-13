Require Import CoqOfRust.lib.lib.

Module error.
  Module ParseBoolError.
    Parameter t : forall `{State.Trait}, Set.
  End ParseBoolError.
  Definition ParseBoolError `{State.Trait} := ParseBoolError.t.
End error.
