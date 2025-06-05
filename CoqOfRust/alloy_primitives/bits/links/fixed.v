Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import alloy_primitives.links.aliases.
Require Export alloy_primitives.bits.links.fixed_FixedBytes.
Require Import alloy_primitives.bits.fixed.
Require Import core.convert.links.mod.
Require Import core.links.array.
Require Import core.links.borrow.
Require Import core.ops.links.deref.
Require Import core.ops.links.index.

Module Impl_FixedBytes.
  Definition Self (N : Usize.t) : Set :=
    FixedBytes.t N.

  (* pub const ZERO: Self *)
  Instance run_zero (N : Usize.t) :
    Run.Trait
      (bits.fixed.Impl_alloy_primitives_bits_fixed_FixedBytes_N.value_ZERO (φ N)) [] [] []
      (Ref.t Pointer.Kind.Raw (Self N)).
  Proof.
    constructor.
  Admitted.

  (* pub fn new(bytes: [u8; N]) -> Self *)
  Instance run_new (N : Usize.t) (bytes: array.t U8.t N) :
    Run.Trait
      (bits.fixed.Impl_alloy_primitives_bits_fixed_FixedBytes_N.new (φ N)) [] [] [φ bytes]
      (Self N).
  Proof.
    constructor.
    run_symbolic.
  Admitted.
End Impl_FixedBytes.
Export Impl_FixedBytes.

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

(* impl<const N: usize> Borrow<[u8; N]> for FixedBytes<N> *)
Module Impl_Borrow_Array_u8_N_for_FixedBytes_N.
  Definition Self (N : Usize.t) : Set :=
    FixedBytes.t N.

  Instance run (N : Usize.t) : Borrow.Run (Self N) (array.t U8.t N).
  Admitted.
End Impl_Borrow_Array_u8_N_for_FixedBytes_N.
Export Impl_Borrow_Array_u8_N_for_FixedBytes_N.

(* impl<const N: usize> DerefMut for FixedBytes<N> *)
Module Impl_DerefMut_for_FixedBytes_N.
  Definition Self (N : Usize.t) : Set :=
    FixedBytes.t N.

  Definition Target (N : Usize.t) : Set :=
    array.t U8.t N.

  Instance run (N : Usize.t) : DerefMut.Run (Self N) (Target N).
  Admitted.
End Impl_DerefMut_for_FixedBytes_N.
Export Impl_DerefMut_for_FixedBytes_N.

Module Impl_Index_for_FixedBytes_N.
  Definition Self (N : Usize.t) : Set :=
    FixedBytes.t N.

  (* type Output = <[u8; N] as Index<__IdxT>>::Output *)
  Definition Output : Set :=
    list U8.t.

  Instance run (N : Usize.t) (__IdxT : Set) `{Link __IdxT} : Index.Run (Self N) __IdxT Output.
  Admitted.
End Impl_Index_for_FixedBytes_N.
Export Impl_Index_for_FixedBytes_N.
