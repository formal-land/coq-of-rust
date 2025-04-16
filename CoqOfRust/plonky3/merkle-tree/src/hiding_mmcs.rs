use alloc::vec::Vec;
use core::cell::RefCell;

use itertools::Itertools;
use p3_commit::Mmcs;
use p3_field::PackedValue;
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::stack::HorizontalPair;
use p3_matrix::{Dimensions, Matrix};
use p3_symmetric::{CryptographicHasher, Hash, PseudoCompressionFunction};
use p3_util::zip_eq::zip_eq;
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};
use serde::de::DeserializeOwned;
use serde::{Deserialize, Serialize};

use crate::{MerkleTree, MerkleTreeError, MerkleTreeMmcs};

/// A vector commitment scheme backed by a `MerkleTree`.
///
/// This is similar to `MerkleTreeMmcs`, but each leaf is "salted" with random elements. This is
/// done to turn the Merkle tree into a hiding commitment. See e.g. Section 3 of
/// [Interactive Oracle Proofs](https://eprint.iacr.org/2016/116).
///
/// `SALT_ELEMS` should be set such that the product of `SALT_ELEMS` with the size of the value
/// (`P::Value`) is at least the target security parameter.
///
/// `R` should be an appropriately seeded cryptographically secure pseudorandom number generator
/// (CSPRNG). Something like `ThreadRng` may work, although it relies on the operating system to
/// provide sufficient entropy.
///
/// Generics:
/// - `P`: a leaf value
/// - `PW`: an element of a digest
/// - `H`: the leaf hasher
/// - `C`: the digest compression function
/// - `R`: a random number generator for blinding leaves
#[derive(Clone, Debug)]
pub struct MerkleTreeHidingMmcs<P, PW, H, C, R, const DIGEST_ELEMS: usize, const SALT_ELEMS: usize>
{
    inner: MerkleTreeMmcs<P, PW, H, C, DIGEST_ELEMS>,
    rng: RefCell<R>,
}

impl<P, PW, H, C, R, const DIGEST_ELEMS: usize, const SALT_ELEMS: usize>
    MerkleTreeHidingMmcs<P, PW, H, C, R, DIGEST_ELEMS, SALT_ELEMS>
{
    pub fn new(hash: H, compress: C, rng: R) -> Self {
        let inner = MerkleTreeMmcs::new(hash, compress);
        Self {
            inner,
            rng: rng.into(),
        }
    }
}

impl<P, PW, H, C, R, const DIGEST_ELEMS: usize, const SALT_ELEMS: usize> Mmcs<P::Value>
    for MerkleTreeHidingMmcs<P, PW, H, C, R, DIGEST_ELEMS, SALT_ELEMS>
where
    P: PackedValue,
    P::Value: Serialize + DeserializeOwned,
    PW: PackedValue,
    H: CryptographicHasher<P::Value, [PW::Value; DIGEST_ELEMS]>
        + CryptographicHasher<P, [PW; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[PW::Value; DIGEST_ELEMS], 2>
        + PseudoCompressionFunction<[PW; DIGEST_ELEMS], 2>
        + Sync,
    R: Rng + Clone,
    PW::Value: Eq,
    [PW::Value; DIGEST_ELEMS]: Serialize + for<'de> Deserialize<'de>,
    StandardUniform: Distribution<P::Value>,
{
    type ProverData<M> =
        MerkleTree<P::Value, PW::Value, HorizontalPair<M, RowMajorMatrix<P::Value>>, DIGEST_ELEMS>;
    type Commitment = Hash<P::Value, PW::Value, DIGEST_ELEMS>;
    /// The first item is salts; the second is the usual Merkle proof (sibling digests).
    type Proof = (Vec<Vec<P::Value>>, Vec<[PW::Value; DIGEST_ELEMS]>);
    type Error = MerkleTreeError;

    fn commit<M: Matrix<P::Value>>(
        &self,
        inputs: Vec<M>,
    ) -> (Self::Commitment, Self::ProverData<M>) {
        let salted_inputs = inputs
            .into_iter()
            .map(|mat| {
                let salts =
                    RowMajorMatrix::rand(&mut *self.rng.borrow_mut(), mat.height(), SALT_ELEMS);
                HorizontalPair::new(mat, salts)
            })
            .collect();
        self.inner.commit(salted_inputs)
    }

    fn open_batch<M: Matrix<P::Value>>(
        &self,
        index: usize,
        prover_data: &Self::ProverData<M>,
    ) -> (Vec<Vec<P::Value>>, Self::Proof) {
        let (salted_openings, siblings) = self.inner.open_batch(index, prover_data);
        let (openings, salts): (Vec<_>, Vec<_>) = salted_openings
            .into_iter()
            .map(|row| {
                let (a, b) = row.split_at(row.len() - SALT_ELEMS);
                (a.to_vec(), b.to_vec())
            })
            .unzip();
        (openings, (salts, siblings))
    }

    fn get_matrices<'a, M: Matrix<P::Value>>(
        &self,
        prover_data: &'a Self::ProverData<M>,
    ) -> Vec<&'a M> {
        prover_data.leaves.iter().map(|mat| &mat.first).collect()
    }

    fn verify_batch(
        &self,
        commit: &Self::Commitment,
        dimensions: &[Dimensions],
        index: usize,
        opened_values: &[Vec<P::Value>],
        proof: &Self::Proof,
    ) -> Result<(), Self::Error> {
        let (salts, siblings) = proof;

        let opened_salted_values = zip_eq(opened_values, salts, MerkleTreeError::WrongBatchSize)?
            .map(|(opened, salt)| opened.iter().chain(salt.iter()).copied().collect_vec())
            .collect_vec();

        self.inner
            .verify_batch(commit, dimensions, index, &opened_salted_values, siblings)
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use itertools::Itertools;
    use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
    use p3_commit::Mmcs;
    use p3_field::{Field, PrimeCharacteristicRing};
    use p3_matrix::Matrix;
    use p3_matrix::dense::RowMajorMatrix;
    use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    use super::MerkleTreeHidingMmcs;
    use crate::MerkleTreeError;

    type F = BabyBear;
    const SALT_ELEMS: usize = 4;

    type Perm = Poseidon2BabyBear<16>;
    type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
    type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
    type MyMmcs = MerkleTreeHidingMmcs<
        <F as Field>::Packing,
        <F as Field>::Packing,
        MyHash,
        MyCompress,
        SmallRng,
        8,
        SALT_ELEMS,
    >;

    #[test]
    #[should_panic]
    fn mismatched_heights() {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash, compress, rng);

        // attempt to commit to a mat with 8 rows and a mat with 7 rows. this should panic.
        let large_mat = RowMajorMatrix::new([1, 2, 3, 4, 5, 6, 7, 8].map(F::from_u8).to_vec(), 1);
        let small_mat = RowMajorMatrix::new([1, 2, 3, 4, 5, 6, 7].map(F::from_u8).to_vec(), 1);
        let _ = mmcs.commit(vec![large_mat, small_mat]);
    }

    #[test]
    fn different_widths() -> Result<(), MerkleTreeError> {
        let mut rng = SmallRng::seed_from_u64(1);
        // 10 mats with 32 rows where the ith mat has i + 1 cols
        let mats = (0..10)
            .map(|i| RowMajorMatrix::<F>::rand(&mut rng, 32, i + 1))
            .collect_vec();
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash, compress, rng);

        let dims = mats.iter().map(|m| m.dimensions()).collect_vec();

        let (commit, prover_data) = mmcs.commit(mats);
        let (opened_values, proof) = mmcs.open_batch(17, &prover_data);
        mmcs.verify_batch(&commit, &dims, 17, &opened_values, &proof)
    }
}
