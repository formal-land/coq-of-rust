use alloc::string::String;
use core::marker::PhantomData;

use itertools::Itertools;
use p3_field::{Field, PrimeField, PrimeField32, reduce_32};

use crate::hasher::CryptographicHasher;
use crate::permutation::CryptographicPermutation;

/// A padding-free, overwrite-mode sponge function.
///
/// `WIDTH` is the sponge's rate plus the sponge's capacity.
#[derive(Copy, Clone, Debug)]
pub struct PaddingFreeSponge<P, const WIDTH: usize, const RATE: usize, const OUT: usize> {
    permutation: P,
}

impl<P, const WIDTH: usize, const RATE: usize, const OUT: usize>
    PaddingFreeSponge<P, WIDTH, RATE, OUT>
{
    pub const fn new(permutation: P) -> Self {
        Self { permutation }
    }
}

impl<T, P, const WIDTH: usize, const RATE: usize, const OUT: usize> CryptographicHasher<T, [T; OUT]>
    for PaddingFreeSponge<P, WIDTH, RATE, OUT>
where
    T: Default + Copy,
    P: CryptographicPermutation<[T; WIDTH]>,
{
    fn hash_iter<I>(&self, input: I) -> [T; OUT]
    where
        I: IntoIterator<Item = T>,
    {
        // static_assert(RATE < WIDTH)
        let mut state = [T::default(); WIDTH];
        let mut input = input.into_iter();

        // Itertools' chunks() is more convenient, but seems to add more overhead,
        // hence the more manual loop.
        'outer: loop {
            for i in 0..RATE {
                if let Some(x) = input.next() {
                    state[i] = x;
                } else {
                    if i != 0 {
                        self.permutation.permute_mut(&mut state);
                    }
                    break 'outer;
                }
            }
            self.permutation.permute_mut(&mut state);
        }

        state[..OUT].try_into().unwrap()
    }
}

/// A padding-free, overwrite-mode sponge function that operates natively over PF but accepts elements
/// of F: PrimeField32.
///
/// `WIDTH` is the sponge's rate plus the sponge's capacity.
#[derive(Clone, Debug)]
pub struct MultiField32PaddingFreeSponge<
    F,
    PF,
    P,
    const WIDTH: usize,
    const RATE: usize,
    const OUT: usize,
> {
    permutation: P,
    num_f_elms: usize,
    _phantom: PhantomData<(F, PF)>,
}

impl<F, PF, P, const WIDTH: usize, const RATE: usize, const OUT: usize>
    MultiField32PaddingFreeSponge<F, PF, P, WIDTH, RATE, OUT>
where
    F: PrimeField32,
    PF: Field,
{
    pub fn new(permutation: P) -> Result<Self, String> {
        if F::order() >= PF::order() {
            return Err(String::from("F::order() must be less than PF::order()"));
        }

        let num_f_elms = PF::bits() / F::bits();
        Ok(Self {
            permutation,
            num_f_elms,
            _phantom: PhantomData,
        })
    }
}

impl<F, PF, P, const WIDTH: usize, const RATE: usize, const OUT: usize>
    CryptographicHasher<F, [PF; OUT]> for MultiField32PaddingFreeSponge<F, PF, P, WIDTH, RATE, OUT>
where
    F: PrimeField32,
    PF: PrimeField + Default + Copy,
    P: CryptographicPermutation<[PF; WIDTH]>,
{
    fn hash_iter<I>(&self, input: I) -> [PF; OUT]
    where
        I: IntoIterator<Item = F>,
    {
        let mut state = [PF::default(); WIDTH];
        for block_chunk in &input.into_iter().chunks(RATE) {
            for (chunk_id, chunk) in (&block_chunk.chunks(self.num_f_elms))
                .into_iter()
                .enumerate()
            {
                state[chunk_id] = reduce_32(&chunk.collect_vec());
            }
            state = self.permutation.permute(state);
        }

        state[..OUT].try_into().unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Permutation;

    #[derive(Clone)]
    struct MockPermutation;

    impl<T, const WIDTH: usize> Permutation<[T; WIDTH]> for MockPermutation
    where
        T: Copy + core::ops::Add<Output = T> + Default,
    {
        fn permute_mut(&self, input: &mut [T; WIDTH]) {
            let sum: T = input.iter().copied().fold(T::default(), |acc, x| acc + x);
            // Set every element to the sum
            *input = [sum; WIDTH];
        }
    }

    impl<T, const WIDTH: usize> CryptographicPermutation<[T; WIDTH]> for MockPermutation where
        T: Copy + core::ops::Add<Output = T> + Default
    {
    }

    #[test]
    fn test_padding_free_sponge_basic() {
        const WIDTH: usize = 4;
        const RATE: usize = 2;
        const OUT: usize = 2;

        let permutation = MockPermutation;
        let sponge = PaddingFreeSponge::<MockPermutation, WIDTH, RATE, OUT>::new(permutation);

        let input = [1, 2, 3, 4, 5];
        let output = sponge.hash_iter(input);

        // Explanation of why the final state results in [44, 44, 44, 44]:
        // Initial state: [0, 0, 0, 0]
        // First input chunk [1, 2] overwrites first two positions: [1, 2, 0, 0]
        // Apply permutation (sum all elements and overwrite): [3, 3, 3, 3]
        // Second input chunk [3, 4] overwrites first two positions: [3, 4, 3, 3]
        // Apply permutation: [13, 13, 13, 13] (3 + 4 + 3 + 3 = 13)
        // Third input chunk [5] overwrites first position: [5, 13, 13, 13]
        // Apply permutation: [44, 44, 44, 44] (5 + 13 + 13 + 13 = 44)

        assert_eq!(output, [44; OUT]);
    }

    #[test]
    fn test_padding_free_sponge_empty_input() {
        const WIDTH: usize = 4;
        const RATE: usize = 2;
        const OUT: usize = 2;

        let permutation = MockPermutation;
        let sponge = PaddingFreeSponge::<MockPermutation, WIDTH, RATE, OUT>::new(permutation);

        let input: [u64; 0] = [];
        let output = sponge.hash_iter(input);

        assert_eq!(
            output, [0; OUT],
            "Should return default values when input is empty."
        );
    }

    #[test]
    fn test_padding_free_sponge_exact_block_size() {
        const WIDTH: usize = 6;
        const RATE: usize = 3;
        const OUT: usize = 2;

        let permutation = MockPermutation;
        let sponge = PaddingFreeSponge::<MockPermutation, WIDTH, RATE, OUT>::new(permutation);

        let input = [10, 20, 30];
        let output = sponge.hash_iter(input);

        let expected_sum = 10 + 20 + 30;
        assert_eq!(output, [expected_sum; OUT]);
    }
}
