Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.alloc.

Module Global.
  Parameter t : Set.
End Global.
Definition Global := Global.t.

Global Instance Allocator_for_Global :
  core.alloc.Allocator.Trait Global.
Admitted.
