//! The Poseidon permutation.

#![no_std]

extern crate alloc;

use alloc::vec::Vec;

use p3_field::{Algebra, InjectiveMonomial, PrimeField};
use p3_mds::MdsPermutation;
use p3_symmetric::{CryptographicPermutation, Permutation};
use rand::Rng;
use rand::distr::StandardUniform;
use rand::prelude::Distribution;

/// The Poseidon permutation.
#[derive(Clone, Debug)]
pub struct Poseidon<F, Mds, const WIDTH: usize, const ALPHA: u64> {
    half_num_full_rounds: usize,
    num_partial_rounds: usize,
    constants: Vec<F>,
    mds: Mds,
}

impl<F, Mds, const WIDTH: usize, const ALPHA: u64> Poseidon<F, Mds, WIDTH, ALPHA>
where
    F: PrimeField + InjectiveMonomial<ALPHA>,
{
    /// Create a new Poseidon configuration.
    ///
    /// # Panics
    /// Number of constants must match WIDTH times `num_rounds`; panics otherwise.
    pub fn new(
        half_num_full_rounds: usize,
        num_partial_rounds: usize,
        constants: Vec<F>,
        mds: Mds,
    ) -> Self {
        let num_rounds = 2 * half_num_full_rounds + num_partial_rounds;
        assert_eq!(constants.len(), WIDTH * num_rounds);
        Self {
            half_num_full_rounds,
            num_partial_rounds,
            constants,
            mds,
        }
    }

    pub fn new_from_rng<R: Rng>(
        half_num_full_rounds: usize,
        num_partial_rounds: usize,
        mds: Mds,
        rng: &mut R,
    ) -> Self
    where
        StandardUniform: Distribution<F>,
    {
        let num_rounds = 2 * half_num_full_rounds + num_partial_rounds;
        let num_constants = WIDTH * num_rounds;
        let constants = rng
            .sample_iter(StandardUniform)
            .take(num_constants)
            .collect::<Vec<_>>();
        Self {
            half_num_full_rounds,
            num_partial_rounds,
            constants,
            mds,
        }
    }

    fn half_full_rounds<A>(&self, state: &mut [A; WIDTH], round_ctr: &mut usize)
    where
        A: Algebra<F> + InjectiveMonomial<ALPHA>,
        Mds: MdsPermutation<A, WIDTH>,
    {
        for _ in 0..self.half_num_full_rounds {
            self.constant_layer(state, *round_ctr);
            Self::full_sbox_layer(state);
            self.mds.permute_mut(state);
            *round_ctr += 1;
        }
    }

    fn partial_rounds<A>(&self, state: &mut [A; WIDTH], round_ctr: &mut usize)
    where
        A: Algebra<F> + InjectiveMonomial<ALPHA>,
        Mds: MdsPermutation<A, WIDTH>,
    {
        for _ in 0..self.num_partial_rounds {
            self.constant_layer(state, *round_ctr);
            Self::partial_sbox_layer(state);
            self.mds.permute_mut(state);
            *round_ctr += 1;
        }
    }

    fn full_sbox_layer<A>(state: &mut [A; WIDTH])
    where
        A: Algebra<F> + InjectiveMonomial<ALPHA>,
    {
        for x in state.iter_mut() {
            *x = x.injective_exp_n();
        }
    }

    fn partial_sbox_layer<A>(state: &mut [A; WIDTH])
    where
        A: Algebra<F> + InjectiveMonomial<ALPHA>,
    {
        state[0] = state[0].injective_exp_n();
    }

    fn constant_layer<A>(&self, state: &mut [A; WIDTH], round: usize)
    where
        A: Algebra<F>,
    {
        for (i, x) in state.iter_mut().enumerate() {
            *x += self.constants[round * WIDTH + i];
        }
    }
}

impl<F, A, Mds, const WIDTH: usize, const ALPHA: u64> Permutation<[A; WIDTH]>
    for Poseidon<F, Mds, WIDTH, ALPHA>
where
    F: PrimeField + InjectiveMonomial<ALPHA>,
    A: Algebra<F> + InjectiveMonomial<ALPHA>,
    Mds: MdsPermutation<A, WIDTH>,
{
    fn permute_mut(&self, state: &mut [A; WIDTH]) {
        let mut round_ctr = 0;
        self.half_full_rounds(state, &mut round_ctr);
        self.partial_rounds(state, &mut round_ctr);
        self.half_full_rounds(state, &mut round_ctr);
    }
}

impl<F, A, Mds, const WIDTH: usize, const ALPHA: u64> CryptographicPermutation<[A; WIDTH]>
    for Poseidon<F, Mds, WIDTH, ALPHA>
where
    F: PrimeField + InjectiveMonomial<ALPHA>,
    A: Algebra<F> + InjectiveMonomial<ALPHA>,
    Mds: MdsPermutation<A, WIDTH>,
{
}
