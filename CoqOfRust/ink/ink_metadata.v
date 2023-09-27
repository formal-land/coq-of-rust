Require Import CoqOfRust.CoqOfRust.

Module layout.
  Module Layout.
    Parameter t : Set -> Set.

    Module Default.
      Parameter F : Set.
    End Default.
  End Layout.
  Definition Layout := Layout.t.
End layout.
