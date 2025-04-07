Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.links.aliases.
Require Export alloy_primitives.bits.links.fixed_FixedBytes.
Require Import alloy_primitives.bits.fixed.
Require Import core.convert.links.mod.
Require Import core.links.array.

Module Impl_FixedBytes.
  Definition Self (N: Usize.t) : Set :=
    FixedBytes.t N.

  (* pub const ZERO: Self *)
  Instance run_zero (N: Usize.t) :
    Run.Trait
      (bits.fixed.Impl_alloy_primitives_bits_fixed_FixedBytes_N.value_ZERO (φ N)) [] [] []
      (Self N).
  Proof.
    constructor.
  Admitted.

  (* pub fn new(bytes: [u8; N]) -> Self *)
  Instance run_new (N: Usize.t) (bytes: array.t U8.t N) :
    Run.Trait
      (bits.fixed.Impl_alloy_primitives_bits_fixed_FixedBytes_N.new (φ N)) [] [] [φ bytes]
      (Self N).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_FixedBytes.

Module Impl_From_FixedBytes_32_for_U256.
  Definition Self : Set :=
    aliases.U256.t.

  Definition run_from : From.Run_from Self (FixedBytes.t {| Integer.value := 32 |}).
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply bits.fixed.Impl_core_convert_From_alloy_primitives_bits_fixed_FixedBytes_Usize_32_for_ruint_Uint_Usize_256_Usize_4.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
      all: admit.
    }
  Admitted.

  Instance run : From.Run Self (FixedBytes.t {| Integer.value := 32 |}) :=
  {
    From.from := run_from;
  }.
End Impl_From_FixedBytes_32_for_U256.
Export Impl_From_FixedBytes_32_for_U256.

Module Impl_From_U256_for_FixedBytes_32.
  Definition Self : Set :=
    FixedBytes.t {| Integer.value := 32 |}.

  Instance run : From.Run Self aliases.U256.t.
  Admitted.
End Impl_From_U256_for_FixedBytes_32.
Export Impl_From_U256_for_FixedBytes_32.
