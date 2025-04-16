use p3_air::{Air, AirBuilder, BaseAir};
use p3_blake3_air::Blake3Air;
use p3_challenger::FieldChallenger;
use p3_commit::PolynomialSpace;
use p3_field::{ExtensionField, Field, PrimeField64};
use p3_keccak_air::KeccakAir;
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2::GenericPoseidon2LinearLayers;
use p3_poseidon2_air::{Poseidon2Air, VectorizedPoseidon2Air};
use p3_uni_stark::{
    DebugConstraintBuilder, ProverConstraintFolder, StarkGenericConfig, SymbolicAirBuilder,
    SymbolicExpression, VerifierConstraintFolder,
};
use rand::distr::StandardUniform;
use rand::prelude::Distribution;

/// An enum containing the three different AIR's.
///
/// This implements `AIR` by passing to whatever the contained struct is.
pub enum ProofObjective<
    F: Field,
    LinearLayers,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
    const VECTOR_LEN: usize,
> {
    Blake3(Blake3Air),
    Keccak(KeccakAir),
    Poseidon2(
        VectorizedPoseidon2Air<
            F,
            LinearLayers,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
            VECTOR_LEN,
        >,
    ),
}

/// An AIR for a hash function used for example proofs and benchmarking.
///
/// A key feature is the ability to randomly generate a trace which proves
/// the output of some number of hashes using a given hash function.
pub trait ExampleHashAir<F: Field, SC: StarkGenericConfig>:
    BaseAir<F>
    + for<'a> Air<DebugConstraintBuilder<'a, F>>
    + Air<SymbolicAirBuilder<F>>
    + for<'a> Air<ProverConstraintFolder<'a, SC>>
    + for<'a> Air<VerifierConstraintFolder<'a, SC>>
{
    fn generate_trace_rows(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F>
    where
        StandardUniform: Distribution<F>;
}

impl<
    F: Field,
    LinearLayers: Sync,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
    const VECTOR_LEN: usize,
> BaseAir<F>
    for ProofObjective<
        F,
        LinearLayers,
        WIDTH,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS,
        VECTOR_LEN,
    >
{
    #[inline]
    fn width(&self) -> usize {
        match self {
            Self::Blake3(b3_air) => <Blake3Air as BaseAir<F>>::width(b3_air),
            Self::Poseidon2(p2_air) => p2_air.width(),
            Self::Keccak(k_air) => <KeccakAir as BaseAir<F>>::width(k_air),
        }
    }
}

impl<
    AB: AirBuilder,
    LinearLayers: GenericPoseidon2LinearLayers<AB::Expr, WIDTH>,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
    const VECTOR_LEN: usize,
> Air<AB>
    for ProofObjective<
        AB::F,
        LinearLayers,
        WIDTH,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS,
        VECTOR_LEN,
    >
{
    #[inline]
    fn eval(&self, builder: &mut AB) {
        match self {
            Self::Blake3(b3_air) => b3_air.eval(builder),
            Self::Poseidon2(p2_air) => p2_air.eval(builder),
            Self::Keccak(k_air) => k_air.eval(builder),
        }
    }
}

impl<
    F: PrimeField64,
    Domain: PolynomialSpace<Val = F>,
    EF: ExtensionField<F>,
    Challenger: FieldChallenger<F>,
    Pcs: p3_commit::Pcs<EF, Challenger, Domain = Domain>,
    SC: StarkGenericConfig<Pcs = Pcs, Challenge = EF, Challenger = Challenger>,
    LinearLayers: GenericPoseidon2LinearLayers<F, WIDTH>
        + GenericPoseidon2LinearLayers<SymbolicExpression<F>, WIDTH>
        + GenericPoseidon2LinearLayers<<F as Field>::Packing, WIDTH>
        + GenericPoseidon2LinearLayers<EF, WIDTH>,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
    const VECTOR_LEN: usize,
> ExampleHashAir<F, SC>
    for ProofObjective<
        F,
        LinearLayers,
        WIDTH,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS,
        VECTOR_LEN,
    >
{
    #[inline]
    fn generate_trace_rows(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F>
    where
        StandardUniform: Distribution<F>,
    {
        match self {
            Self::Blake3(b3_air) => b3_air.generate_trace_rows(num_hashes, extra_capacity_bits),
            Self::Poseidon2(p2_air) => {
                p2_air.generate_vectorized_trace_rows(num_hashes, extra_capacity_bits)
            }
            Self::Keccak(k_air) => k_air.generate_trace_rows(num_hashes, extra_capacity_bits),
        }
    }
}

impl<
    F: PrimeField64,
    Domain: PolynomialSpace<Val = F>,
    EF: ExtensionField<F>,
    Challenger: FieldChallenger<F>,
    Pcs: p3_commit::Pcs<EF, Challenger, Domain = Domain>,
    SC: StarkGenericConfig<Pcs = Pcs, Challenge = EF, Challenger = Challenger>,
> ExampleHashAir<F, SC> for Blake3Air
{
    #[inline]
    fn generate_trace_rows(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F>
    where
        StandardUniform: Distribution<F>,
    {
        self.generate_trace_rows(num_hashes, extra_capacity_bits)
    }
}

impl<
    F: PrimeField64,
    Domain: PolynomialSpace<Val = F>,
    EF: ExtensionField<F>,
    Challenger: FieldChallenger<F>,
    Pcs: p3_commit::Pcs<EF, Challenger, Domain = Domain>,
    SC: StarkGenericConfig<Pcs = Pcs, Challenge = EF, Challenger = Challenger>,
> ExampleHashAir<F, SC> for KeccakAir
{
    #[inline]
    fn generate_trace_rows(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F>
    where
        StandardUniform: Distribution<F>,
    {
        self.generate_trace_rows(num_hashes, extra_capacity_bits)
    }
}

impl<
    F: PrimeField64,
    Domain: PolynomialSpace<Val = F>,
    EF: ExtensionField<F>,
    Challenger: FieldChallenger<F>,
    Pcs: p3_commit::Pcs<EF, Challenger, Domain = Domain>,
    SC: StarkGenericConfig<Pcs = Pcs, Challenge = EF, Challenger = Challenger>,
    LinearLayers: GenericPoseidon2LinearLayers<F, WIDTH>
        + GenericPoseidon2LinearLayers<SymbolicExpression<F>, WIDTH>
        + GenericPoseidon2LinearLayers<<F as Field>::Packing, WIDTH>
        + GenericPoseidon2LinearLayers<EF, WIDTH>,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
    const VECTOR_LEN: usize,
> ExampleHashAir<F, SC>
    for VectorizedPoseidon2Air<
        F,
        LinearLayers,
        WIDTH,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS,
        VECTOR_LEN,
    >
{
    #[inline]
    fn generate_trace_rows(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F>
    where
        StandardUniform: Distribution<F>,
    {
        self.generate_vectorized_trace_rows(num_hashes, extra_capacity_bits)
    }
}

impl<
    F: PrimeField64,
    Domain: PolynomialSpace<Val = F>,
    EF: ExtensionField<F>,
    Challenger: FieldChallenger<F>,
    Pcs: p3_commit::Pcs<EF, Challenger, Domain = Domain>,
    SC: StarkGenericConfig<Pcs = Pcs, Challenge = EF, Challenger = Challenger>,
    LinearLayers: GenericPoseidon2LinearLayers<F, WIDTH>
        + GenericPoseidon2LinearLayers<SymbolicExpression<F>, WIDTH>
        + GenericPoseidon2LinearLayers<<F as Field>::Packing, WIDTH>
        + GenericPoseidon2LinearLayers<EF, WIDTH>,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
> ExampleHashAir<F, SC>
    for Poseidon2Air<
        F,
        LinearLayers,
        WIDTH,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS,
    >
{
    #[inline]
    fn generate_trace_rows(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F>
    where
        StandardUniform: Distribution<F>,
    {
        self.generate_trace_rows(num_hashes, extra_capacity_bits)
    }
}
