use alloc::string::String;
use alloc::vec;
use alloc::vec::Vec;

use p3_field::{BasedVectorSpace, Field, PrimeField, PrimeField32, reduce_32, split_32};
use p3_symmetric::{CryptographicPermutation, Hash};

use crate::{CanObserve, CanSample, CanSampleBits, FieldChallenger};

/// A challenger that operates natively on PF but produces challenges of F: PrimeField32.
///
/// Used for optimizing the cost of recursive proof verification of STARKs in SNARKs.
///
/// SAFETY: There are some bias complications with using this challenger. In particular,
/// samples are actually random in [0, 2^64) and then reduced to be in F.
#[derive(Clone, Debug)]
pub struct MultiField32Challenger<F, PF, P, const WIDTH: usize, const RATE: usize>
where
    F: PrimeField32,
    PF: Field,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    sponge_state: [PF; WIDTH],
    input_buffer: Vec<F>,
    output_buffer: Vec<F>,
    permutation: P,
    num_f_elms: usize,
}

impl<F, PF, P, const WIDTH: usize, const RATE: usize> MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    PF: Field,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    pub fn new(permutation: P) -> Result<Self, String> {
        if F::order() >= PF::order() {
            return Err(String::from("F::order() must be less than PF::order()"));
        }
        let num_f_elms = PF::bits() / 64;
        Ok(Self {
            sponge_state: [PF::default(); WIDTH],
            input_buffer: vec![],
            output_buffer: vec![],
            permutation,
            num_f_elms,
        })
    }
}

impl<F, PF, P, const WIDTH: usize, const RATE: usize> MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    PF: PrimeField,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn duplexing(&mut self) {
        assert!(self.input_buffer.len() <= self.num_f_elms * RATE);

        for (i, f_chunk) in self.input_buffer.chunks(self.num_f_elms).enumerate() {
            self.sponge_state[i] = reduce_32(f_chunk);
        }
        self.input_buffer.clear();

        // Apply the permutation.
        self.permutation.permute_mut(&mut self.sponge_state);

        self.output_buffer.clear();
        for &pf_val in &self.sponge_state {
            let f_vals = split_32(pf_val, self.num_f_elms);
            for f_val in f_vals {
                self.output_buffer.push(f_val);
            }
        }
    }
}

impl<F, PF, P, const WIDTH: usize, const RATE: usize> FieldChallenger<F>
    for MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    PF: PrimeField,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
}

impl<F, PF, P, const WIDTH: usize, const RATE: usize> CanObserve<F>
    for MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    PF: PrimeField,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn observe(&mut self, value: F) {
        // Any buffered output is now invalid.
        self.output_buffer.clear();

        self.input_buffer.push(value);

        if self.input_buffer.len() == self.num_f_elms * RATE {
            self.duplexing();
        }
    }
}

impl<F, PF, const N: usize, P, const WIDTH: usize, const RATE: usize> CanObserve<[F; N]>
    for MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    PF: PrimeField,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn observe(&mut self, values: [F; N]) {
        for value in values {
            self.observe(value);
        }
    }
}

impl<F, PF, const N: usize, P, const WIDTH: usize, const RATE: usize> CanObserve<Hash<F, PF, N>>
    for MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    PF: PrimeField,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn observe(&mut self, values: Hash<F, PF, N>) {
        for pf_val in values {
            let f_vals: Vec<F> = split_32(pf_val, self.num_f_elms);
            for f_val in f_vals {
                self.observe(f_val);
            }
        }
    }
}

// for TrivialPcs
impl<F, PF, P, const WIDTH: usize, const RATE: usize> CanObserve<Vec<Vec<F>>>
    for MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    PF: PrimeField,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn observe(&mut self, valuess: Vec<Vec<F>>) {
        for values in valuess {
            for value in values {
                self.observe(value);
            }
        }
    }
}

impl<F, EF, PF, P, const WIDTH: usize, const RATE: usize> CanSample<EF>
    for MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    EF: BasedVectorSpace<F>,
    PF: PrimeField,
    P: CryptographicPermutation<[PF; WIDTH]>,
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

impl<F, PF, P, const WIDTH: usize, const RATE: usize> CanSampleBits<usize>
    for MultiField32Challenger<F, PF, P, WIDTH, RATE>
where
    F: PrimeField32,
    PF: PrimeField,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn sample_bits(&mut self, bits: usize) -> usize {
        assert!(bits < (usize::BITS as usize));
        assert!((1 << bits) < F::ORDER_U32);
        let rand_f: F = self.sample();
        let rand_usize = rand_f.as_canonical_u32() as usize;
        rand_usize & ((1 << bits) - 1)
    }
}
