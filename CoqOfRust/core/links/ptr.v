Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.

Require Import core.ptr.mod.
Import core.ptr.mod.ptr.

Definition run_write_volatile (T: Set) `{Link T} (dst: Ref.t Pointer.Kind.MutRef T) (src: T) :
    Run.Trait
        write_volatile [] [] [φ dst] unit.
Proof.
Admitted.

