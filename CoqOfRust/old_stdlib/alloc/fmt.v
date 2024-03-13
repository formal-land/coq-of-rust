Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.string.
Require CoqOfRust.core.fmt.

Parameter format :
  M.Val core.fmt.Arguments.t ->
  M (M.Val alloc.string.String.t).
