Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import pinocchio.memory.
Require Import pinocchio.links.lib.

Instance run_sol_memcpy
  (dst : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8)))
  (src : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8)))
  (n : Usize.t) :
  Run.Trait
    memory.sol_memcpy
    [] []
    [φ dst; φ src; φ n]
    unit.
Proof.
  constructor.
  admit.
Admitted.

Instance run_copy_val
  (A : Set) `{Link A}
  (dst : Ref.t Pointer.Kind.Ref A)
  (src : Ref.t Pointer.Kind.Ref A) :
  Run.Trait
    memory.copy_val
    [] []
    [φ dst; φ src]
    unit.
Proof.
  constructor.
  admit.
Admitted.

Instance run_sol_memmove
  (dst : Ref.t Pointer.Kind.Raw U8.t)
  (src : Ref.t Pointer.Kind.Raw U8.t)
  (n : Usize.t) :
  Run.Trait
    memory.sol_memmove
    [] []
    [φ dst; φ src; φ n]
    unit.
Proof.
  constructor.
  admit.
Admitted.

Instance run_sol_memcmp
  (s1 : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8)))
  (s2 : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8)))
  (n : Usize.t) :
  Run.Trait
    memory.sol_memcmp
    [] []
    [φ s1; φ s2; φ n]
    I32.t.
Proof.
  constructor.
  admit.
Admitted.

Instance run_sol_memset
  (s : Ref.t Pointer.Kind.Ref (list (Integer.t IntegerKind.U8)))
  (c : U8.t)
  (n : Usize.t) :
  Run.Trait
    memory.sol_memset
    [] []
    [φ s; φ c; φ n]
    unit.
Proof.
  constructor.
  admit.
Admitted.
