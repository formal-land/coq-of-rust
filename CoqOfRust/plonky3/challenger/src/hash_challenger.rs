use alloc::vec;
use alloc::vec::Vec;

use p3_symmetric::CryptographicHasher;

use crate::{CanObserve, CanSample};

/// A generic challenger that uses a cryptographic hash function to generate challenges.
#[derive(Clone, Debug)]
pub struct HashChallenger<T, H, const OUT_LEN: usize>
where
    T: Clone,
    H: CryptographicHasher<T, [T; OUT_LEN]>,
{
    /// Buffer to store observed values before hashing.
    input_buffer: Vec<T>,
    /// Buffer to store hashed output values, which are consumed when sampling.
    output_buffer: Vec<T>,
    /// The cryptographic hash function used for generating challenges.
    hasher: H,
}

impl<T, H, const OUT_LEN: usize> HashChallenger<T, H, OUT_LEN>
where
    T: Clone,
    H: CryptographicHasher<T, [T; OUT_LEN]>,
{
    pub const fn new(initial_state: Vec<T>, hasher: H) -> Self {
        Self {
            input_buffer: initial_state,
            output_buffer: vec![],
            hasher,
        }
    }

    fn flush(&mut self) {
        let inputs = self.input_buffer.drain(..);
        let output = self.hasher.hash_iter(inputs);

        self.output_buffer = output.to_vec();

        // Chaining values.
        self.input_buffer.extend(output.to_vec());
    }
}

impl<T, H, const OUT_LEN: usize> CanObserve<T> for HashChallenger<T, H, OUT_LEN>
where
    T: Clone,
    H: CryptographicHasher<T, [T; OUT_LEN]>,
{
    fn observe(&mut self, value: T) {
        // Any buffered output is now invalid.
        self.output_buffer.clear();

        self.input_buffer.push(value);
    }
}

impl<T, H, const N: usize, const OUT_LEN: usize> CanObserve<[T; N]>
    for HashChallenger<T, H, OUT_LEN>
where
    T: Clone,
    H: CryptographicHasher<T, [T; OUT_LEN]>,
{
    fn observe(&mut self, values: [T; N]) {
        for value in values {
            self.observe(value);
        }
    }
}

impl<T, H, const OUT_LEN: usize> CanSample<T> for HashChallenger<T, H, OUT_LEN>
where
    T: Clone,
    H: CryptographicHasher<T, [T; OUT_LEN]>,
{
    fn sample(&mut self) -> T {
        if self.output_buffer.is_empty() {
            self.flush();
        }
        self.output_buffer
            .pop()
            .expect("Output buffer should be non-empty")
    }
}

#[cfg(test)]
mod tests {
    use p3_field::PrimeCharacteristicRing;
    use p3_goldilocks::Goldilocks;

    use super::*;

    const OUT_LEN: usize = 2;
    type F = Goldilocks;

    #[derive(Clone)]
    struct TestHasher {}

    impl CryptographicHasher<F, [F; OUT_LEN]> for TestHasher {
        /// A very simple hash iterator. From an input of type `IntoIterator<Item = Goldilocks>`,
        /// it outputs the sum of its elements and its length (as a field element).
        fn hash_iter<I>(&self, input: I) -> [F; OUT_LEN]
        where
            I: IntoIterator<Item = F>,
        {
            let (sum, len) = input
                .into_iter()
                .fold((F::ZERO, 0_usize), |(acc_sum, acc_len), f| {
                    (acc_sum + f, acc_len + 1)
                });
            [sum, F::from_usize(len)]
        }

        /// A very simple slice hash iterator. From an input of type `IntoIterator<Item = &'a [Goldilocks]>`,
        /// it outputs the sum of its elements and its length (as a field element).
        fn hash_iter_slices<'a, I>(&self, input: I) -> [F; OUT_LEN]
        where
            I: IntoIterator<Item = &'a [F]>,
            F: 'a,
        {
            let (sum, len) = input
                .into_iter()
                .fold((F::ZERO, 0_usize), |(acc_sum, acc_len), n| {
                    (
                        acc_sum + n.iter().fold(F::ZERO, |acc, f| acc + *f),
                        acc_len + n.len(),
                    )
                });
            [sum, F::from_usize(len)]
        }
    }

    #[test]
    fn test_hash_challenger() {
        let initial_state = (1..11_u8).map(F::from_u8).collect::<Vec<_>>();
        let test_hasher = TestHasher {};
        let mut hash_challenger = HashChallenger::new(initial_state.clone(), test_hasher);

        assert_eq!(hash_challenger.input_buffer, initial_state);
        assert_eq!(hash_challenger.output_buffer, vec![]);

        hash_challenger.flush();

        let expected_sum = F::from_u8(55);
        let expected_len = F::from_u8(10);
        assert_eq!(
            hash_challenger.input_buffer,
            vec![expected_sum, expected_len]
        );
        assert_eq!(
            hash_challenger.output_buffer,
            vec![expected_sum, expected_len]
        );

        let new_element = F::from_u8(11);
        hash_challenger.observe(new_element);
        assert_eq!(
            hash_challenger.input_buffer,
            vec![expected_sum, expected_len, new_element]
        );
        assert_eq!(hash_challenger.output_buffer, vec![]);

        let new_expected_len = 3;
        let new_expected_sum = 76;

        let new_element = hash_challenger.sample();
        assert_eq!(new_element, F::from_u8(new_expected_len));
        assert_eq!(
            hash_challenger.output_buffer,
            [F::from_u8(new_expected_sum)]
        )
    }

    #[test]
    fn test_hash_challenger_flush() {
        let initial_state = (1..11_u8).map(F::from_u8).collect::<Vec<_>>();
        let test_hasher = TestHasher {};
        let mut hash_challenger = HashChallenger::new(initial_state, test_hasher);

        // Sample twice to ensure flush happens
        let first_sample = hash_challenger.sample();

        let second_sample = hash_challenger.sample();

        // Verify that the first sample is the length of 1..11, (i.e. 10).
        assert_eq!(first_sample, F::from_u8(10));
        //  Verify that the second sample is the sum of numbers from 1 to 10 (i.e. 55)
        assert_eq!(second_sample, F::from_u8(55));

        // Verify that the output buffer is now empty
        assert!(hash_challenger.output_buffer.is_empty());
    }

    #[test]
    fn test_observe_single_value() {
        let test_hasher = TestHasher {};
        // Initial state non-empty
        let mut hash_challenger = HashChallenger::new(vec![F::from_u8(123)], test_hasher);

        // Observe a single value
        let value = F::from_u8(42);
        hash_challenger.observe(value);

        // Check that the input buffer contains the initial and observed values
        assert_eq!(
            hash_challenger.input_buffer,
            vec![F::from_u8(123), F::from_u8(42)]
        );
        // Check that the output buffer is empty (clears after observation)
        assert!(hash_challenger.output_buffer.is_empty());
    }

    #[test]
    fn test_observe_array() {
        let test_hasher = TestHasher {};
        // Initial state non-empty
        let mut hash_challenger = HashChallenger::new(vec![F::from_u8(123)], test_hasher);

        // Observe an array of values
        let values = [F::from_u8(1), F::from_u8(2), F::from_u8(3)];
        hash_challenger.observe(values);

        // Check that the input buffer contains the values
        assert_eq!(
            hash_challenger.input_buffer,
            vec![F::from_u8(123), F::from_u8(1), F::from_u8(2), F::from_u8(3)]
        );
        // Check that the output buffer is empty (clears after observation)
        assert!(hash_challenger.output_buffer.is_empty());
    }

    #[test]
    fn test_sample_output_buffer() {
        let test_hasher = TestHasher {};
        let initial_state = vec![F::from_u8(5), F::from_u8(10)];
        let mut hash_challenger = HashChallenger::new(initial_state, test_hasher);

        let sample = hash_challenger.sample();
        // Verify that the sample is the length of the initial state
        assert_eq!(sample, F::from_u8(2));
        // Check that the output buffer contains the sum of the initial state
        assert_eq!(hash_challenger.output_buffer, vec![F::from_u8(15)]);
    }

    #[test]
    fn test_flush_empty_buffer() {
        let test_hasher = TestHasher {};
        let mut hash_challenger = HashChallenger::new(vec![], test_hasher);

        // Flush empty buffer
        hash_challenger.flush();

        // Check that the input and output buffers contain the sum and length of the empty buffer
        assert_eq!(hash_challenger.input_buffer, vec![F::ZERO, F::ZERO]);
        assert_eq!(hash_challenger.output_buffer, vec![F::ZERO, F::ZERO]);
    }

    #[test]
    fn test_flush_with_data() {
        let test_hasher = TestHasher {};
        // Initial state non-empty
        let initial_state = vec![F::from_u8(1), F::from_u8(2)];
        let mut hash_challenger = HashChallenger::new(initial_state, test_hasher);

        hash_challenger.flush();

        // Check that the input buffer contains the sum and length of the initial state
        assert_eq!(
            hash_challenger.input_buffer,
            vec![F::from_u8(3), F::from_u8(2)]
        );
        // Check that the output buffer contains the sum and length of the initial state
        assert_eq!(
            hash_challenger.output_buffer,
            vec![F::from_u8(3), F::from_u8(2)]
        );
    }

    #[test]
    fn test_sample_after_observe() {
        let test_hasher = TestHasher {};
        let initial_state = vec![F::from_u8(1), F::from_u8(2)];
        let mut hash_challenger = HashChallenger::new(initial_state, test_hasher);

        // Observe will clear the output buffer
        hash_challenger.observe(F::from_u8(3));

        // Verify that the output buffer is empty
        assert!(hash_challenger.output_buffer.is_empty());

        // Verify the new value is in the input buffer
        assert_eq!(
            hash_challenger.input_buffer,
            vec![F::from_u8(1), F::from_u8(2), F::from_u8(3)]
        );

        let sample = hash_challenger.sample();

        // Length of initial state + observed value
        assert_eq!(sample, F::from_u8(3));
    }

    #[test]
    fn test_sample_with_non_empty_output_buffer() {
        let test_hasher = TestHasher {};
        let mut hash_challenger = HashChallenger::new(vec![], test_hasher);

        hash_challenger.output_buffer = vec![F::from_u8(42), F::from_u8(24)];

        let sample = hash_challenger.sample();

        // Sample will pop the last element from the output buffer
        assert_eq!(sample, F::from_u8(24));

        // Check that the output buffer is now one element shorter
        assert_eq!(hash_challenger.output_buffer, vec![F::from_u8(42)]);
    }

    #[test]
    fn test_output_buffer_cleared_on_observe() {
        let test_hasher = TestHasher {};
        let mut hash_challenger = HashChallenger::new(vec![], test_hasher);

        // Populate artificially the output buffer
        hash_challenger.output_buffer.push(F::from_u8(42));

        // Ensure the output buffer is populated
        assert!(!hash_challenger.output_buffer.is_empty());

        // Observe a new value
        hash_challenger.observe(F::from_u8(3));

        // Verify that the output buffer is cleared after observing
        assert!(hash_challenger.output_buffer.is_empty());
    }
}
