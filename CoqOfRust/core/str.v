Require Import CoqOfRust.lib.lib.

Module error.
  Module ParseBoolError.
    Parameter t : Set.
  End ParseBoolError.
  Definition ParseBoolError := ParseBoolError.t.
End error.
