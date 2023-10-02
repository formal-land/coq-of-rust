Require Import CoqOfRust.CoqOfRust.

Module error.
  Parameter Error : Set.

  Parameter Result : Set -> Set.
End error.

Module item.
  Parameter ItemFn : Set.
End item.

Module path.
  Parameter Path : Set.
End path.
