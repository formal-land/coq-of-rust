Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import plonky3.keccak_air.lib.

(* pub const NUM_ROUNDS: usize = 24; *)
Definition NUM_ROUNDS : Usize.t :=
  {| Integer.value := 24 |}.

Instance run_value_NUM_ROUNDS :
  Run.Trait lib.value_NUM_ROUNDS [] [] [] (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.

(* const BITS_PER_LIMB: usize = 16; *)
Definition BITS_PER_LIMB : Usize.t :=
  {| Integer.value := 16 |}.

Instance run_value_BITS_PER_LIMB :
  Run.Trait lib.value_BITS_PER_LIMB [] [] [] (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.

(* pub const U64_LIMBS: usize = 64 / BITS_PER_LIMB; *)
Definition U64_LIMBS : Usize.t :=
  {| Integer.value := 64 / BITS_PER_LIMB.(Integer.value) |}.

Instance run_value_U64_LIMBS :
  Run.Trait lib.value_U64_LIMBS [] [] [] (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.

(* const RATE_BITS: usize = 1088; *)
Definition RATE_BITS : Usize.t :=
  {| Integer.value := 1088 |}.

Instance run_value_RATE_BITS :
  Run.Trait lib.value_RATE_BITS [] [] [] (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.

(* const RATE_LIMBS: usize = RATE_BITS / BITS_PER_LIMB; *)
Definition RATE_LIMBS : Usize.t :=
  {| Integer.value := RATE_BITS.(Integer.value) / BITS_PER_LIMB.(Integer.value) |}.

Instance run_value_RATE_LIMBS :
  Run.Trait lib.value_RATE_LIMBS [] [] [] (Ref.t Pointer.Kind.Raw Usize.t).
Proof.
  constructor.
  run_symbolic.
Defined.
