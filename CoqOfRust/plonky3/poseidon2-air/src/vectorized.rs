use core::borrow::{Borrow, BorrowMut};

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{Field, PrimeField};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_poseidon2::GenericPoseidon2LinearLayers;
use rand::distr::StandardUniform;
use rand::prelude::Distribution;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

use crate::air::eval;
use crate::constants::RoundConstants;
use crate::{Poseidon2Air, Poseidon2Cols, generate_vectorized_trace_rows};

/// A "vectorized" version of Poseidon2Cols, for computing multiple Poseidon2 permutations per row.
#[repr(C)]
pub struct VectorizedPoseidon2Cols<
    T,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
    const VECTOR_LEN: usize,
> {
    pub(crate) cols:
        [Poseidon2Cols<T, WIDTH, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>;
            VECTOR_LEN],
}

impl<
    T,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
    const VECTOR_LEN: usize,
>
    Borrow<
        VectorizedPoseidon2Cols<
            T,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
            VECTOR_LEN,
        >,
    > for [T]
{
    fn borrow(
        &self,
    ) -> &VectorizedPoseidon2Cols<
        T,
        WIDTH,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS,
        VECTOR_LEN,
    > {
        // debug_assert_eq!(self.len(), NUM_COLS);
        let (prefix, shorts, suffix) = unsafe {
            self.align_to::<VectorizedPoseidon2Cols<
                T,
                WIDTH,
                SBOX_DEGREE,
                SBOX_REGISTERS,
                HALF_FULL_ROUNDS,
                PARTIAL_ROUNDS,
                VECTOR_LEN,
            >>()
        };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &shorts[0]
    }
}

impl<
    T,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
    const VECTOR_LEN: usize,
>
    BorrowMut<
        VectorizedPoseidon2Cols<
            T,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
            VECTOR_LEN,
        >,
    > for [T]
{
    fn borrow_mut(
        &mut self,
    ) -> &mut VectorizedPoseidon2Cols<
        T,
        WIDTH,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS,
        VECTOR_LEN,
    > {
        // debug_assert_eq!(self.len(), NUM_COLS);
        let (prefix, shorts, suffix) = unsafe {
            self.align_to_mut::<VectorizedPoseidon2Cols<
                T,
                WIDTH,
                SBOX_DEGREE,
                SBOX_REGISTERS,
                HALF_FULL_ROUNDS,
                PARTIAL_ROUNDS,
                VECTOR_LEN,
            >>()
        };
        debug_assert!(prefix.is_empty(), "Alignment should match");
        debug_assert!(suffix.is_empty(), "Alignment should match");
        debug_assert_eq!(shorts.len(), 1);
        &mut shorts[0]
    }
}

/// A "vectorized" version of Poseidon2Air, for computing multiple Poseidon2 permutations per row.
pub struct VectorizedPoseidon2Air<
    F: Field,
    LinearLayers,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
    const VECTOR_LEN: usize,
> {
    pub(crate) air: Poseidon2Air<
        F,
        LinearLayers,
        WIDTH,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS,
    >,
}

impl<
    F: Field,
    LinearLayers,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
    const VECTOR_LEN: usize,
>
    VectorizedPoseidon2Air<
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
    pub const fn new(
        constants: RoundConstants<F, WIDTH, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>,
    ) -> Self {
        Self {
            air: Poseidon2Air::new(constants),
        }
    }

    pub fn generate_vectorized_trace_rows(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F>
    where
        F: PrimeField,
        LinearLayers: GenericPoseidon2LinearLayers<F, WIDTH>,
        StandardUniform: Distribution<[F; WIDTH]>,
    {
        let mut rng = SmallRng::seed_from_u64(1);
        let inputs = (0..num_hashes).map(|_| rng.random()).collect();
        generate_vectorized_trace_rows::<
            _,
            LinearLayers,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
            VECTOR_LEN,
        >(inputs, &self.air.constants, extra_capacity_bits)
    }
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
    fn width(&self) -> usize {
        self.air.width() * VECTOR_LEN
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
    for VectorizedPoseidon2Air<
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
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &VectorizedPoseidon2Cols<
            _,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
            VECTOR_LEN,
        > = (*local).borrow();
        for perm in &local.cols {
            eval(&self.air, builder, perm);
        }
    }
}
