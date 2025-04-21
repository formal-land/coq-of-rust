use alloc::vec;
use alloc::vec::Vec;

use p3_field::{BasedVectorSpace, Field, PrimeField64};
use p3_symmetric::{CryptographicPermutation, Hash};

use crate::{CanObserve, CanSample, CanSampleBits, FieldChallenger};

#[derive(Clone, Debug)]
pub struct DuplexChallenger<F, P, const WIDTH: usize, const RATE: usize>
where
    F: Clone,
    P: CryptographicPermutation<[F; WIDTH]>,
{
    pub sponge_state: [F; WIDTH],
    pub input_buffer: Vec<F>,
    pub output_buffer: Vec<F>,
    pub permutation: P,
}

impl<F, P, const WIDTH: usize, const RATE: usize> DuplexChallenger<F, P, WIDTH, RATE>
where
    F: Copy,
    P: CryptographicPermutation<[F; WIDTH]>,
{
    pub fn new(permutation: P) -> Self
    where
        F: Default,
    {
        Self {
            sponge_state: [F::default(); WIDTH],
            input_buffer: vec![],
            output_buffer: vec![],
            permutation,
        }
    }

    fn duplexing(&mut self) {
        assert!(self.input_buffer.len() <= RATE);

        // Overwrite the first r elements with the inputs.
        for (i, val) in self.input_buffer.drain(..).enumerate() {
            self.sponge_state[i] = val;
        }

        // Apply the permutation.
        self.permutation.permute_mut(&mut self.sponge_state);

        self.output_buffer.clear();
        self.output_buffer.extend(&self.sponge_state[..RATE]);
    }
}

impl<F, P, const WIDTH: usize, const RATE: usize> FieldChallenger<F>
    for DuplexChallenger<F, P, WIDTH, RATE>
where
    F: PrimeField64,
    P: CryptographicPermutation<[F; WIDTH]>,
{
}

impl<F, P, const WIDTH: usize, const RATE: usize> CanObserve<F>
    for DuplexChallenger<F, P, WIDTH, RATE>
where
    F: Copy,
    P: CryptographicPermutation<[F; WIDTH]>,
{
    fn observe(&mut self, value: F) {
        // Any buffered output is now invalid.
        self.output_buffer.clear();

        self.input_buffer.push(value);

        if self.input_buffer.len() == RATE {
            self.duplexing();
        }
    }
}

impl<F, P, const N: usize, const WIDTH: usize, const RATE: usize> CanObserve<[F; N]>
    for DuplexChallenger<F, P, WIDTH, RATE>
where
    F: Copy,
    P: CryptographicPermutation<[F; WIDTH]>,
{
    fn observe(&mut self, values: [F; N]) {
        for value in values {
            self.observe(value);
        }
    }
}

impl<F, P, const N: usize, const WIDTH: usize, const RATE: usize> CanObserve<Hash<F, F, N>>
    for DuplexChallenger<F, P, WIDTH, RATE>
where
    F: Copy,
    P: CryptographicPermutation<[F; WIDTH]>,
{
    fn observe(&mut self, values: Hash<F, F, N>) {
        for value in values {
            self.observe(value);
        }
    }
}

// for TrivialPcs
impl<F, P, const WIDTH: usize, const RATE: usize> CanObserve<Vec<Vec<F>>>
    for DuplexChallenger<F, P, WIDTH, RATE>
where
    F: Copy,
    P: CryptographicPermutation<[F; WIDTH]>,
{
    fn observe(&mut self, valuess: Vec<Vec<F>>) {
        for values in valuess {
            for value in values {
                self.observe(value);
            }
        }
    }
}

impl<F, EF, P, const WIDTH: usize, const RATE: usize> CanSample<EF>
    for DuplexChallenger<F, P, WIDTH, RATE>
where
    F: Field,
    EF: BasedVectorSpace<F>,
    P: CryptographicPermutation<[F; WIDTH]>,
{
    fn sample(&mut self) -> EF {
        EF::from_basis_coefficients_fn(|_| {
            // If we have buffered inputs, we must perform a duplexing so that the challenge will
            // reflect them. Or if we've run out of outputs, we must perform a duplexing to get more.
            if !self.input_buffer.is_empty() || self.output_buffer.is_empty() {
                self.duplexing();
            }

            self.output_buffer
                .pop()
                .expect("Output buffer should be non-empty")
        })
    }
}

impl<F, P, const WIDTH: usize, const RATE: usize> CanSampleBits<usize>
    for DuplexChallenger<F, P, WIDTH, RATE>
where
    F: PrimeField64,
    P: CryptographicPermutation<[F; WIDTH]>,
{
    fn sample_bits(&mut self, bits: usize) -> usize {
        assert!(bits < (usize::BITS as usize));
        assert!((1 << bits) < F::ORDER_U64);
        let rand_f: F = self.sample();
        let rand_usize = rand_f.as_canonical_u64() as usize;
        rand_usize & ((1 << bits) - 1)
    }
}

#[cfg(test)]
mod tests {
    use core::iter;

    use p3_baby_bear::BabyBear;
    use p3_field::PrimeCharacteristicRing;
    use p3_goldilocks::Goldilocks;
    use p3_symmetric::Permutation;

    use super::*;
    use crate::grinding_challenger::GrindingChallenger;

    const WIDTH: usize = 24;
    const RATE: usize = 16;

    type G = Goldilocks;
    type BB = BabyBear;

    #[derive(Clone)]
    struct TestPermutation {}

    impl<F: Clone> Permutation<[F; WIDTH]> for TestPermutation {
        fn permute_mut(&self, input: &mut [F; WIDTH]) {
            input.reverse()
        }
    }

    impl<F: Clone> CryptographicPermutation<[F; WIDTH]> for TestPermutation {}

    #[test]
    fn test_duplex_challenger() {
        type Chal = DuplexChallenger<G, TestPermutation, WIDTH, RATE>;
        let permutation = TestPermutation {};
        let mut duplex_challenger = DuplexChallenger::new(permutation);

        // Observe 12 elements.
        (0..12).for_each(|element| duplex_challenger.observe(G::from_u8(element as u8)));

        let state_after_duplexing: Vec<_> = iter::repeat_n(G::ZERO, 12)
            .chain((0..12).map(G::from_u8).rev())
            .collect();

        let expected_samples: Vec<G> = state_after_duplexing[..16].iter().copied().rev().collect();
        let samples = <Chal as CanSample<G>>::sample_vec(&mut duplex_challenger, 16);
        assert_eq!(samples, expected_samples);
    }

    #[test]
    #[should_panic]
    fn test_duplex_challenger_sample_bits_security() {
        type GoldilocksChal = DuplexChallenger<G, TestPermutation, WIDTH, RATE>;
        let permutation = TestPermutation {};
        let mut duplex_challenger = GoldilocksChal::new(permutation);

        for _ in 0..100 {
            assert!(duplex_challenger.sample_bits(129) < 4);
        }
    }

    #[test]
    #[should_panic]
    fn test_duplex_challenger_sample_bits_security_small_field() {
        type BabyBearChal = DuplexChallenger<BB, TestPermutation, WIDTH, RATE>;
        let permutation = TestPermutation {};
        let mut duplex_challenger = BabyBearChal::new(permutation);

        for _ in 0..100 {
            assert!(duplex_challenger.sample_bits(40) < 1 << 31);
        }
    }

    #[test]
    #[should_panic]
    fn test_duplex_challenger_grind_security() {
        type GoldilocksChal = DuplexChallenger<G, TestPermutation, WIDTH, RATE>;
        let permutation = TestPermutation {};
        let mut duplex_challenger = GoldilocksChal::new(permutation);

        // This should cause sample_bits (and hence grind and check_witness) to
        // panic. If bit sizes were not constrained correctly inside the
        // challenger, (1 << too_many_bits) would loop around, incorrectly
        // grinding and accepting a 1-bit PoW.
        let too_many_bits = usize::BITS as usize;

        let witness = duplex_challenger.grind(too_many_bits);
        assert!(duplex_challenger.check_witness(too_many_bits, witness));
    }
}
