Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.string.
Require CoqOfRust.core.fmt.

Parameter format :
  forall `{H : State.Trait},
  core.fmt.Arguments -> M (H := H) alloc.string.String.
