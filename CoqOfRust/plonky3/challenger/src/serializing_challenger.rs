use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_field::{BasedVectorSpace, PrimeField32, PrimeField64};
use p3_maybe_rayon::prelude::*;
use p3_symmetric::{CryptographicHasher, Hash};
use p3_util::log2_ceil_u64;
use tracing::instrument;

use crate::{
    CanObserve, CanSample, CanSampleBits, FieldChallenger, GrindingChallenger, HashChallenger,
};

/// Given a challenger that can observe and sample bytes, produces a challenger that is able to
/// sample and observe field elements of a `PrimeField32`.
///
/// **Observing**:
/// -  Takes a field element will serialize it into a byte array and observe each byte.
///
/// **Sampling**:
/// -  Samples a field element in a prime field of size `p` by sampling uniformly an element in the
///    range (0..1 << log_2(p)). This avoids modulo bias.
#[derive(Clone, Debug)]
pub struct SerializingChallenger32<F, Inner> {
    inner: Inner,
    _marker: PhantomData<F>,
}

/// Given a challenger that can observe and sample bytes, produces a challenger that is able to
/// sample and observe field elements of a `PrimeField64` field.
///
/// **Observing**:
/// -  Takes a field element will serialize it into a byte array and observe each byte.
///
/// **Sampling**:
/// -  Samples a field element in a prime field of size `p` by sampling uniformly an element in the
///    range (0..1 << log_2(p)). This avoids modulo bias.
#[derive(Clone, Debug)]
pub struct SerializingChallenger64<F, Inner> {
    inner: Inner,
    _marker: PhantomData<F>,
}

impl<F: PrimeField32, Inner: CanObserve<u8>> SerializingChallenger32<F, Inner> {
    pub const fn new(inner: Inner) -> Self {
        Self {
            inner,
            _marker: PhantomData,
        }
    }
}

impl<F, H> SerializingChallenger32<F, HashChallenger<u8, H, 32>>
where
    F: PrimeField32,
    H: CryptographicHasher<u8, [u8; 32]>,
{
    pub const fn from_hasher(initial_state: Vec<u8>, hasher: H) -> Self {
        Self::new(HashChallenger::new(initial_state, hasher))
    }
}

impl<F: PrimeField32, Inner: CanObserve<u8>> CanObserve<F> for SerializingChallenger32<F, Inner> {
    fn observe(&mut self, value: F) {
        self.inner
            .observe_slice(&value.to_unique_u32().to_le_bytes());
    }
}

impl<F: PrimeField32, const N: usize, Inner: CanObserve<u8>> CanObserve<Hash<F, u8, N>>
    for SerializingChallenger32<F, Inner>
{
    fn observe(&mut self, values: Hash<F, u8, N>) {
        for value in values {
            self.inner.observe(value);
        }
    }
}

impl<F: PrimeField32, const N: usize, Inner: CanObserve<u8>> CanObserve<Hash<F, u64, N>>
    for SerializingChallenger32<F, Inner>
{
    fn observe(&mut self, values: Hash<F, u64, N>) {
        for value in values {
            self.inner.observe_slice(&value.to_le_bytes());
        }
    }
}

impl<F, EF, Inner> CanSample<EF> for SerializingChallenger32<F, Inner>
where
    F: PrimeField32,
    EF: BasedVectorSpace<F>,
    Inner: CanSample<u8>,
{
    fn sample(&mut self) -> EF {
        let modulus = F::ORDER_U32;
        let log_size = log2_ceil_u64(F::ORDER_U64);
        // We use u64 to avoid overflow in the case that log_size = 32.
        let pow_of_two_bound = ((1u64 << log_size) - 1) as u32;
        // Perform rejection sampling over the uniform range (0..log2_ceil(p))
        let sample_base = |inner: &mut Inner| loop {
            let value = u32::from_le_bytes(inner.sample_array());
            let value = value & pow_of_two_bound;
            if value < modulus {
                return unsafe {
                    // This is safe as value < F::ORDER_U32.
                    F::from_canonical_unchecked(value)
                };
            }
        };
        EF::from_basis_coefficients_fn(|_| sample_base(&mut self.inner))
    }
}

impl<F, Inner> CanSampleBits<usize> for SerializingChallenger32<F, Inner>
where
    F: PrimeField32,
    Inner: CanSample<u8>,
{
    fn sample_bits(&mut self, bits: usize) -> usize {
        assert!(bits < (usize::BITS as usize));
        // Limiting the number of bits to the field size
        assert!((1 << bits) <= F::ORDER_U64 as usize);
        let rand_usize = u32::from_le_bytes(self.inner.sample_array()) as usize;
        rand_usize & ((1 << bits) - 1)
    }
}

impl<F, Inner> GrindingChallenger for SerializingChallenger32<F, Inner>
where
    F: PrimeField32,
    Inner: CanSample<u8> + CanObserve<u8> + Clone + Send + Sync,
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

impl<F, Inner> FieldChallenger<F> for SerializingChallenger32<F, Inner>
where
    F: PrimeField32,
    Inner: CanSample<u8> + CanObserve<u8> + Clone + Send + Sync,
{
}

impl<F: PrimeField64, Inner: CanObserve<u8>> SerializingChallenger64<F, Inner> {
    pub const fn new(inner: Inner) -> Self {
        Self {
            inner,
            _marker: PhantomData,
        }
    }
}

impl<F, H> SerializingChallenger64<F, HashChallenger<u8, H, 32>>
where
    F: PrimeField64,
    H: CryptographicHasher<u8, [u8; 32]>,
{
    pub const fn from_hasher(initial_state: Vec<u8>, hasher: H) -> Self {
        Self::new(HashChallenger::new(initial_state, hasher))
    }
}

impl<F: PrimeField64, Inner: CanObserve<u8>> CanObserve<F> for SerializingChallenger64<F, Inner> {
    fn observe(&mut self, value: F) {
        self.inner
            .observe_slice(&value.to_unique_u64().to_le_bytes());
    }
}

impl<F: PrimeField64, const N: usize, Inner: CanObserve<u8>> CanObserve<Hash<F, u8, N>>
    for SerializingChallenger64<F, Inner>
{
    fn observe(&mut self, values: Hash<F, u8, N>) {
        for value in values {
            self.inner.observe(value);
        }
    }
}

impl<F: PrimeField64, const N: usize, Inner: CanObserve<u8>> CanObserve<Hash<F, u64, N>>
    for SerializingChallenger64<F, Inner>
{
    fn observe(&mut self, values: Hash<F, u64, N>) {
        for value in values {
            self.inner.observe_slice(&value.to_le_bytes());
        }
    }
}

impl<F, EF, Inner> CanSample<EF> for SerializingChallenger64<F, Inner>
where
    F: PrimeField64,
    EF: BasedVectorSpace<F>,
    Inner: CanSample<u8>,
{
    fn sample(&mut self) -> EF {
        let modulus = F::ORDER_U64;
        let log_size = log2_ceil_u64(F::ORDER_U64) as u32;
        // We use u128 to avoid overflow in the case that log_size = 64.
        let pow_of_two_bound = ((1u128 << log_size) - 1) as u64;

        // Perform rejection sampling over the uniform range (0..log2_ceil(p))
        let sample_base = |inner: &mut Inner| loop {
            let value = u64::from_le_bytes(inner.sample_array());
            let value = value & pow_of_two_bound;
            if value < modulus {
                return unsafe {
                    // This is safe as value < F::ORDER_U64.
                    F::from_canonical_unchecked(value)
                };
            }
        };
        EF::from_basis_coefficients_fn(|_| sample_base(&mut self.inner))
    }
}

impl<F, Inner> CanSampleBits<usize> for SerializingChallenger64<F, Inner>
where
    F: PrimeField64,
    Inner: CanSample<u8>,
{
    fn sample_bits(&mut self, bits: usize) -> usize {
        assert!(bits < (usize::BITS as usize));
        // Limiting the number of bits to the field size
        assert!((1 << bits) <= F::ORDER_U64 as usize);
        let rand_usize = u64::from_le_bytes(self.inner.sample_array()) as usize;
        rand_usize & ((1 << bits) - 1)
    }
}

impl<F, Inner> GrindingChallenger for SerializingChallenger64<F, Inner>
where
    F: PrimeField64,
    Inner: CanSample<u8> + CanObserve<u8> + Clone + Send + Sync,
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

impl<F, Inner> FieldChallenger<F> for SerializingChallenger64<F, Inner>
where
    F: PrimeField64,
    Inner: CanSample<u8> + CanObserve<u8> + Clone + Send + Sync,
{
}
