//! A MerkleTreeMmcs is a generalization of the standard MerkleTree commitment scheme which supports
//! committing to several matrices of different dimensions.
//!
//! Say we wish to commit to 2 matrices M and N with dimensions (8, i) and (2, j) respectively.
//! Let H denote the hash function and C the compression function for our tree.
//! Then MerkleTreeMmcs produces a commitment to M and N using the following tree structure:
//!
//! ```rust,ignore
//! ///
//! ///                                      root = c00 = C(c10, c11)                              
//! ///                       /                                                \         
//! ///         c10 = C(C(c20, c21), H(N[0]))                     c11 = C(C(c22, c23), H(N[1]))
//! ///           /                      \                          /                      \     
//! ///      c20 = C(L, R)            c21 = C(L, R)            c22 = C(L, R)            c23 = C(L, R)  
//! ///   L/             \R        L/             \R        L/             \R        L/             \R     
//! /// H(M[0])         H(M[1])  H(M[2])         H(M[3])  H(M[4])         H(M[5])  H(M[6])         H(M[7])
//! ```
//! E.g. we start by making a standard MerkleTree commitment for each row of M and then add in the rows of N when we
//! get to the correct level. A proof for the values of say `M[5]` and `N[1]` consists of the siblings `H(M[4]), c23, c10`.
//!

use alloc::vec::Vec;
use core::cmp::Reverse;
use core::marker::PhantomData;

use itertools::Itertools;
use p3_commit::Mmcs;
use p3_field::PackedValue;
use p3_matrix::{Dimensions, Matrix};
use p3_symmetric::{CryptographicHasher, Hash, PseudoCompressionFunction};
use p3_util::{log2_ceil_usize, log2_strict_usize};
use serde::{Deserialize, Serialize};

use crate::MerkleTree;
use crate::MerkleTreeError::{
    EmptyBatch, IncompatibleHeights, RootMismatch, WrongBatchSize, WrongHeight,
};

/// A vector commitment scheme backed by a `MerkleTree`.
///
/// Generics:
/// - `P`: a leaf value
/// - `PW`: an element of a digest
/// - `H`: the leaf hasher
/// - `C`: the digest compression function
#[derive(Copy, Clone, Debug)]
pub struct MerkleTreeMmcs<P, PW, H, C, const DIGEST_ELEMS: usize> {
    hash: H,
    compress: C,
    _phantom: PhantomData<(P, PW)>,
}

#[derive(Debug)]
pub enum MerkleTreeError {
    WrongBatchSize,
    WrongWidth,
    WrongHeight {
        log_max_height: usize,
        num_siblings: usize,
    },
    IncompatibleHeights,
    RootMismatch,
    EmptyBatch,
}

impl<P, PW, H, C, const DIGEST_ELEMS: usize> MerkleTreeMmcs<P, PW, H, C, DIGEST_ELEMS> {
    pub const fn new(hash: H, compress: C) -> Self {
        Self {
            hash,
            compress,
            _phantom: PhantomData,
        }
    }
}

impl<P, PW, H, C, const DIGEST_ELEMS: usize> Mmcs<P::Value>
    for MerkleTreeMmcs<P, PW, H, C, DIGEST_ELEMS>
where
    P: PackedValue,
    PW: PackedValue,
    H: CryptographicHasher<P::Value, [PW::Value; DIGEST_ELEMS]>
        + CryptographicHasher<P, [PW; DIGEST_ELEMS]>
        + Sync,
    C: PseudoCompressionFunction<[PW::Value; DIGEST_ELEMS], 2>
        + PseudoCompressionFunction<[PW; DIGEST_ELEMS], 2>
        + Sync,
    PW::Value: Eq,
    [PW::Value; DIGEST_ELEMS]: Serialize + for<'de> Deserialize<'de>,
{
    type ProverData<M> = MerkleTree<P::Value, PW::Value, M, DIGEST_ELEMS>;
    type Commitment = Hash<P::Value, PW::Value, DIGEST_ELEMS>;
    type Proof = Vec<[PW::Value; DIGEST_ELEMS]>;
    type Error = MerkleTreeError;

    fn commit<M: Matrix<P::Value>>(
        &self,
        inputs: Vec<M>,
    ) -> (Self::Commitment, Self::ProverData<M>) {
        let tree = MerkleTree::new::<P, PW, H, C>(&self.hash, &self.compress, inputs);
        let root = tree.root();
        (root, tree)
    }

    /// Opens a batch of rows from committed matrices.
    ///
    /// Returns `(openings, proof)` where `openings` is a vector whose `i`th element is
    /// the `j`th row of the ith matrix `M[i]`, with
    ///     `j == index >> (log2_ceil(max_height) - log2_ceil(M[i].height))`
    /// and `proof` is the vector of sibling Merkle tree nodes allowing the verifier to
    /// reconstruct the committed root.
    fn open_batch<M: Matrix<P::Value>>(
        &self,
        index: usize,
        prover_data: &MerkleTree<P::Value, PW::Value, M, DIGEST_ELEMS>,
    ) -> (Vec<Vec<P::Value>>, Self::Proof) {
        let max_height = self.get_max_height(prover_data);
        let log_max_height = log2_ceil_usize(max_height);

        // Get the matrix rows encountered along the path from the root to the given leaf index.
        let openings = prover_data
            .leaves
            .iter()
            .map(|matrix| {
                let log2_height = log2_ceil_usize(matrix.height());
                let bits_reduced = log_max_height - log2_height;
                let reduced_index = index >> bits_reduced;
                matrix.row(reduced_index).collect()
            })
            .collect_vec();

        // Get all the siblings nodes corresponding to the path from the root to the given leaf index.
        let proof = (0..log_max_height)
            .map(|i| prover_data.digest_layers[i][(index >> i) ^ 1])
            .collect();

        (openings, proof)
    }

    fn get_matrices<'a, M: Matrix<P::Value>>(
        &self,
        prover_data: &'a Self::ProverData<M>,
    ) -> Vec<&'a M> {
        prover_data.leaves.iter().collect()
    }

    /// Verifies an opened batch of rows with respect to a given commitment.
    ///
    /// - `commit`: The merkle root of the tree.
    /// - `dimensions`: A vector of the dimensions of the matrices committed to.
    /// - `index`: The index of a leaf in the tree.
    /// - `opened_values`: A vector of matrix rows. Assume that the tallest matrix committed
    ///   to has height `2^n >= M_tall.height() > 2^{n - 1}` and the `j`th matrix has height
    ///   `2^m >= Mj.height() > 2^{m - 1}`. Then `j`'th value of opened values must be the row `Mj[index >> (m - n)]`.
    /// - `proof`: A vector of sibling nodes. The `i`th element should be the node at level `i`
    ///   with index `(index << i) ^ 1`.
    ///
    /// Returns nothing if the verification is successful, otherwise returns an error.
    fn verify_batch(
        &self,
        commit: &Self::Commitment,
        dimensions: &[Dimensions],
        mut index: usize,
        opened_values: &[Vec<P::Value>],
        proof: &Self::Proof,
    ) -> Result<(), Self::Error> {
        // Check that the openings have the correct shape.
        if dimensions.len() != opened_values.len() {
            return Err(WrongBatchSize);
        }

        // TODO: Disabled for now since TwoAdicFriPcs and CirclePcs currently pass 0 for width.
        // for (dims, opened_vals) in zip_eq(dimensions.iter(), opened_values) {
        //     if opened_vals.len() != dims.width {
        //         return Err(WrongWidth);
        //     }
        // }

        let mut heights_tallest_first = dimensions
            .iter()
            .enumerate()
            .sorted_by_key(|(_, dims)| Reverse(dims.height))
            .peekable();

        // Matrix heights that round up to the same power of two must be equal
        if !heights_tallest_first
            .clone()
            .map(|(_, dims)| dims.height)
            .tuple_windows()
            .all(|(curr, next)| {
                curr == next || curr.next_power_of_two() != next.next_power_of_two()
            })
        {
            return Err(IncompatibleHeights);
        }

        // Get the initial height padded to a power of two. As heights_tallest_first is sorted,
        // the initial height will be the maximum height.
        // Returns an error if either:
        //              1. proof.len() != log_max_height
        //              2. heights_tallest_first is empty.
        let mut curr_height_padded = match heights_tallest_first.peek() {
            Some((_, dims)) => {
                let max_height = dims.height.next_power_of_two();
                let log_max_height = log2_strict_usize(max_height);
                if proof.len() != log_max_height {
                    return Err(WrongHeight {
                        log_max_height,
                        num_siblings: proof.len(),
                    });
                }
                max_height
            }
            None => return Err(EmptyBatch),
        };

        // Hash all matrix openings at the current height.
        let mut root = self.hash.hash_iter_slices(
            heights_tallest_first
                .peeking_take_while(|(_, dims)| {
                    dims.height.next_power_of_two() == curr_height_padded
                })
                .map(|(i, _)| opened_values[i].as_slice()),
        );

        for &sibling in proof {
            // The last bit of index informs us whether the current node is on the left or right.
            let (left, right) = if index & 1 == 0 {
                (root, sibling)
            } else {
                (sibling, root)
            };

            // Combine the current node with the sibling node to get the parent node.
            root = self.compress.compress([left, right]);
            index >>= 1;
            curr_height_padded >>= 1;

            // Check if there are any new matrix rows to inject at the next height.
            let next_height = heights_tallest_first
                .peek()
                .map(|(_, dims)| dims.height)
                .filter(|h| h.next_power_of_two() == curr_height_padded);
            if let Some(next_height) = next_height {
                // If there are new matrix rows, hash the rows together and then combine with the current root.
                let next_height_openings_digest = self.hash.hash_iter_slices(
                    heights_tallest_first
                        .peeking_take_while(|(_, dims)| dims.height == next_height)
                        .map(|(i, _)| opened_values[i].as_slice()),
                );

                root = self.compress.compress([root, next_height_openings_digest]);
            }
        }

        // The computed root should equal the committed one.
        if commit == &root {
            Ok(())
        } else {
            Err(RootMismatch)
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use itertools::Itertools;
    use p3_baby_bear::{BabyBear, Poseidon2BabyBear};
    use p3_commit::Mmcs;
    use p3_field::{Field, PrimeCharacteristicRing};
    use p3_matrix::dense::RowMajorMatrix;
    use p3_matrix::{Dimensions, Matrix};
    use p3_symmetric::{
        CryptographicHasher, PaddingFreeSponge, PseudoCompressionFunction, TruncatedPermutation,
    };
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    use super::MerkleTreeMmcs;

    type F = BabyBear;

    type Perm = Poseidon2BabyBear<16>;
    type MyHash = PaddingFreeSponge<Perm, 16, 8, 8>;
    type MyCompress = TruncatedPermutation<Perm, 2, 8, 16>;
    type MyMmcs =
        MerkleTreeMmcs<<F as Field>::Packing, <F as Field>::Packing, MyHash, MyCompress, 8>;

    #[test]
    fn commit_single_1x8() {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash.clone(), compress.clone());

        // v = [2, 1, 2, 2, 0, 0, 1, 0]
        let v = vec![
            F::TWO,
            F::ONE,
            F::TWO,
            F::TWO,
            F::ZERO,
            F::ZERO,
            F::ONE,
            F::ZERO,
        ];
        let (commit, _) = mmcs.commit_vec(v.clone());

        let expected_result = compress.compress([
            compress.compress([
                compress.compress([hash.hash_item(v[0]), hash.hash_item(v[1])]),
                compress.compress([hash.hash_item(v[2]), hash.hash_item(v[3])]),
            ]),
            compress.compress([
                compress.compress([hash.hash_item(v[4]), hash.hash_item(v[5])]),
                compress.compress([hash.hash_item(v[6]), hash.hash_item(v[7])]),
            ]),
        ]);
        assert_eq!(commit, expected_result);
    }

    #[test]
    fn commit_single_8x1() {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash.clone(), compress);

        let mat = RowMajorMatrix::<F>::rand(&mut rng, 1, 8);
        let (commit, _) = mmcs.commit(vec![mat.clone()]);

        let expected_result = hash.hash_iter(mat.vertically_packed_row(0));
        assert_eq!(commit, expected_result);
    }

    #[test]
    fn commit_single_2x2() {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash.clone(), compress.clone());

        // mat = [
        //   0 1
        //   2 1
        // ]
        let mat = RowMajorMatrix::new(vec![F::ZERO, F::ONE, F::TWO, F::ONE], 2);

        let (commit, _) = mmcs.commit(vec![mat]);

        let expected_result = compress.compress([
            hash.hash_slice(&[F::ZERO, F::ONE]),
            hash.hash_slice(&[F::TWO, F::ONE]),
        ]);
        assert_eq!(commit, expected_result);
    }

    #[test]
    fn commit_single_2x3() {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash.clone(), compress.clone());
        let default_digest = [F::ZERO; 8];

        // mat = [
        //   0 1
        //   2 1
        //   2 2
        // ]
        let mat = RowMajorMatrix::new(vec![F::ZERO, F::ONE, F::TWO, F::ONE, F::TWO, F::TWO], 2);

        let (commit, _) = mmcs.commit(vec![mat]);

        let expected_result = compress.compress([
            compress.compress([
                hash.hash_slice(&[F::ZERO, F::ONE]),
                hash.hash_slice(&[F::TWO, F::ONE]),
            ]),
            compress.compress([hash.hash_slice(&[F::TWO, F::TWO]), default_digest]),
        ]);
        assert_eq!(commit, expected_result);
    }

    #[test]
    fn commit_mixed() {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash.clone(), compress.clone());
        let default_digest = [F::ZERO; 8];

        // mat_1 = [
        //   0 1
        //   2 1
        //   2 2
        //   2 1
        //   2 2
        // ]
        let mat_1 = RowMajorMatrix::new(
            vec![
                F::ZERO,
                F::ONE,
                F::TWO,
                F::ONE,
                F::TWO,
                F::TWO,
                F::TWO,
                F::ONE,
                F::TWO,
                F::TWO,
            ],
            2,
        );
        // mat_2 = [
        //   1 2 1
        //   0 2 2
        //   1 2 1
        // ]
        let mat_2 = RowMajorMatrix::new(
            vec![
                F::ONE,
                F::TWO,
                F::ONE,
                F::ZERO,
                F::TWO,
                F::TWO,
                F::ONE,
                F::TWO,
                F::ONE,
            ],
            3,
        );

        let (commit, prover_data) = mmcs.commit(vec![mat_1, mat_2]);

        let mat_1_leaf_hashes = [
            hash.hash_slice(&[F::ZERO, F::ONE]),
            hash.hash_slice(&[F::TWO, F::ONE]),
            hash.hash_slice(&[F::TWO, F::TWO]),
            hash.hash_slice(&[F::TWO, F::ONE]),
            hash.hash_slice(&[F::TWO, F::TWO]),
        ];
        let mat_2_leaf_hashes = [
            hash.hash_slice(&[F::ONE, F::TWO, F::ONE]),
            hash.hash_slice(&[F::ZERO, F::TWO, F::TWO]),
            hash.hash_slice(&[F::ONE, F::TWO, F::ONE]),
        ];

        let expected_result = compress.compress([
            compress.compress([
                compress.compress([
                    compress.compress([mat_1_leaf_hashes[0], mat_1_leaf_hashes[1]]),
                    mat_2_leaf_hashes[0],
                ]),
                compress.compress([
                    compress.compress([mat_1_leaf_hashes[2], mat_1_leaf_hashes[3]]),
                    mat_2_leaf_hashes[1],
                ]),
            ]),
            compress.compress([
                compress.compress([
                    compress.compress([mat_1_leaf_hashes[4], default_digest]),
                    mat_2_leaf_hashes[2],
                ]),
                default_digest,
            ]),
        ]);

        assert_eq!(commit, expected_result);

        let (opened_values, _proof) = mmcs.open_batch(2, &prover_data);
        assert_eq!(
            opened_values,
            vec![vec![F::TWO, F::TWO], vec![F::ZERO, F::TWO, F::TWO]]
        );
    }

    #[test]
    fn commit_either_order() {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash, compress);

        let input_1 = RowMajorMatrix::<F>::rand(&mut rng, 5, 8);
        let input_2 = RowMajorMatrix::<F>::rand(&mut rng, 3, 16);

        let (commit_1_2, _) = mmcs.commit(vec![input_1.clone(), input_2.clone()]);
        let (commit_2_1, _) = mmcs.commit(vec![input_2, input_1]);
        assert_eq!(commit_1_2, commit_2_1);
    }

    #[test]
    #[should_panic]
    fn mismatched_heights() {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash, compress);

        // attempt to commit to a mat with 8 rows and a mat with 7 rows. this should panic.
        let large_mat = RowMajorMatrix::new([1, 2, 3, 4, 5, 6, 7, 8].map(F::from_u8).to_vec(), 1);
        let small_mat = RowMajorMatrix::new([1, 2, 3, 4, 5, 6, 7].map(F::from_u8).to_vec(), 1);
        let _ = mmcs.commit(vec![large_mat, small_mat]);
    }

    #[test]
    fn verify_tampered_proof_fails() {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash, compress);

        // 4 8x1 matrixes, 4 8x2 matrixes
        let mut mats = (0..4)
            .map(|_| RowMajorMatrix::<F>::rand(&mut rng, 8, 1))
            .collect_vec();
        let large_mat_dims = (0..4).map(|_| Dimensions {
            height: 8,
            width: 1,
        });
        mats.extend((0..4).map(|_| RowMajorMatrix::<F>::rand(&mut rng, 8, 2)));
        let small_mat_dims = (0..4).map(|_| Dimensions {
            height: 8,
            width: 2,
        });

        let (commit, prover_data) = mmcs.commit(mats);

        // open the 3rd row of each matrix, mess with proof, and verify
        let (opened_values, mut proof) = mmcs.open_batch(3, &prover_data);
        proof[0][0] += F::ONE;
        mmcs.verify_batch(
            &commit,
            &large_mat_dims.chain(small_mat_dims).collect_vec(),
            3,
            &opened_values,
            &proof,
        )
        .expect_err("expected verification to fail");
    }

    #[test]
    fn size_gaps() {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash, compress);

        // 4 mats with 1000 rows, 8 columns
        let mut mats = (0..4)
            .map(|_| RowMajorMatrix::<F>::rand(&mut rng, 1000, 8))
            .collect_vec();
        let large_mat_dims = (0..4).map(|_| Dimensions {
            height: 1000,
            width: 8,
        });

        // 5 mats with 70 rows, 8 columns
        mats.extend((0..5).map(|_| RowMajorMatrix::<F>::rand(&mut rng, 70, 8)));
        let medium_mat_dims = (0..5).map(|_| Dimensions {
            height: 70,
            width: 8,
        });

        // 6 mats with 8 rows, 8 columns
        mats.extend((0..6).map(|_| RowMajorMatrix::<F>::rand(&mut rng, 8, 8)));
        let small_mat_dims = (0..6).map(|_| Dimensions {
            height: 8,
            width: 8,
        });

        // 7 tiny mat with 1 row, 8 columns
        mats.extend((0..7).map(|_| RowMajorMatrix::<F>::rand(&mut rng, 1, 8)));
        let tiny_mat_dims = (0..7).map(|_| Dimensions {
            height: 1,
            width: 8,
        });

        let (commit, prover_data) = mmcs.commit(mats);

        // open the 6th row of each matrix and verify
        let (opened_values, proof) = mmcs.open_batch(6, &prover_data);
        mmcs.verify_batch(
            &commit,
            &large_mat_dims
                .chain(medium_mat_dims)
                .chain(small_mat_dims)
                .chain(tiny_mat_dims)
                .collect_vec(),
            6,
            &opened_values,
            &proof,
        )
        .expect("expected verification to succeed");
    }

    #[test]
    fn different_widths() {
        let mut rng = SmallRng::seed_from_u64(1);
        let perm = Perm::new_from_rng_128(&mut rng);
        let hash = MyHash::new(perm.clone());
        let compress = MyCompress::new(perm);
        let mmcs = MyMmcs::new(hash, compress);

        // 10 mats with 32 rows where the ith mat has i + 1 cols
        let mats = (0..10)
            .map(|i| RowMajorMatrix::<F>::rand(&mut rng, 32, i + 1))
            .collect_vec();
        let dims = mats.iter().map(|m| m.dimensions()).collect_vec();

        let (commit, prover_data) = mmcs.commit(mats);
        let (opened_values, proof) = mmcs.open_batch(17, &prover_data);
        mmcs.verify_batch(&commit, &dims, 17, &opened_values, &proof)
            .expect("expected verification to succeed");
    }
}
