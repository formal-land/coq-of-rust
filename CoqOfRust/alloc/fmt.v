Require Import CoqOfRust.lib.lib.

Require CoqOfRust.alloc.string.
Require CoqOfRust.core.fmt.

Parameter format : core.fmt.Arguments -> M alloc.string.String.
