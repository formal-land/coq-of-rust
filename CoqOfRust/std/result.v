Require Import CoqOfRust.lib.lib.

Module Result.
  Inductive t (T E : Set) : Set :=
  | Ok : T -> t T E
  | Err : E -> t T E.
  Arguments Ok {T E} _.
  Arguments Err {T E} _.
End Result.
Definition Result := Result.t.
