/// A permutation in the mathematical sense.
pub trait Permutation<T: Clone>: Clone + Sync {
    #[inline(always)]
    fn permute(&self, mut input: T) -> T {
        self.permute_mut(&mut input);
        input
    }

    fn permute_mut(&self, input: &mut T);
}

/// A permutation thought to be cryptographically secure, in the sense that it is thought to be
/// difficult to distinguish (in a nontrivial way) from a random permutation.
pub trait CryptographicPermutation<T: Clone>: Permutation<T> {}
