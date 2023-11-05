Require Import CoqOfRust.lib.lib.
Require CoqOfRust.core.alloc.

Module Global.
  Parameter t : forall `{State.Trait}, Set.
End Global.
Definition Global `{State.Trait} := Global.t.

Global Instance Allocator_for_Global `{State.Trait} :
  core.alloc.Allocator.Trait Global.
Admitted.
