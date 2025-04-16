use p3_field::{Field, PrimeField, PrimeField32, PrimeField64};
use p3_maybe_rayon::prelude::*;
use p3_symmetric::CryptographicPermutation;
use tracing::instrument;

use crate::{CanObserve, CanSampleBits, DuplexChallenger, MultiField32Challenger};

pub trait GrindingChallenger:
    CanObserve<Self::Witness> + CanSampleBits<usize> + Sync + Clone
{
    type Witness: Field;

    fn grind(&mut self, bits: usize) -> Self::Witness;

    #[must_use]
    fn check_witness(&mut self, bits: usize, witness: Self::Witness) -> bool {
        self.observe(witness);
        self.sample_bits(bits) == 0
    }
}

impl<F, P, const WIDTH: usize, const RATE: usize> GrindingChallenger
    for DuplexChallenger<F, P, WIDTH, RATE>
where
    F: PrimeField64,
    P: CryptographicPermutation<[F; WIDTH]>,
{
    type Witness = F;

    #[instrument(name = "grind for proof-of-work witness", skip_all)]
    fn grind(&mut self, bits: usize) -> Self::Witness {
        assert!(bits < (usize::BITS as usize));
        assert!((1 << bits) < F::ORDER_U64);

        let witness = (0..F::ORDER_U64)
            .into_par_iter()
            .map(|i| unsafe {
                // i < F::ORDER_U64 by construction so this is safe.
                F::from_canonical_unchecked(i)
            })
            .find_any(|witness| self.clone().check_witness(bits, *witness))
            .expect("failed to find witness");
        assert!(self.check_witness(bits, witness));
        witness
    }
}

impl<F, PF, P, const WIDTH: usize, const RATE: usize> GrindingChallenger
    for MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    PF: PrimeField,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    type Witness = F;

    #[instrument(name = "grind for proof-of-work witness", skip_all)]
    fn grind(&mut self, bits: usize) -> Self::Witness {
        assert!(bits < (usize::BITS as usize));
        assert!((1 << bits) < F::ORDER_U32);
        let witness = (0..F::ORDER_U32)
            .into_par_iter()
            .map(|i| unsafe {
                // i < F::ORDER_U32 by construction so this is safe.
                F::from_canonical_unchecked(i)
            })
            .find_any(|witness| self.clone().check_witness(bits, *witness))
            .expect("failed to find witness");
        assert!(self.check_witness(bits, witness));
        witness
    }
}
