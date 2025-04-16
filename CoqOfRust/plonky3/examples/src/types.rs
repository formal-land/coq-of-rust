//! This contains a large number of type definitions which help simplify the code in other files and keep clippy happy.
//!
//! In particular this builds up to defining the types `KeccakStarkConfig`,
//! `KeccakCircleStarkConfig`, `Poseidon2StarkConfig`, `Poseidon2CircleStarkConfig`.
//! These are needed to define our proof functions.

use p3_challenger::{DuplexChallenger, HashChallenger, SerializingChallenger32};
use p3_circle::CirclePcs;
use p3_commit::ExtensionMmcs;
use p3_field::Field;
use p3_fri::TwoAdicFriPcs;
use p3_keccak::{Keccak256Hash, KeccakF};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{
    CompressionFunctionFromHasher, PaddingFreeSponge, SerializingHasher32To64, TruncatedPermutation,
};
use p3_uni_stark::StarkConfig;

// Types related to using Keccak in the Merkle tree.
const KECCAK_VECTOR_LEN: usize = p3_keccak::VECTOR_LEN;
pub(crate) type KeccakCompressionFunction =
    CompressionFunctionFromHasher<PaddingFreeSponge<KeccakF, 25, 17, 4>, 2, 4>;
pub(crate) type KeccakMerkleMmcs<F> = MerkleTreeMmcs<
    [F; KECCAK_VECTOR_LEN],
    [u64; KECCAK_VECTOR_LEN],
    SerializingHasher32To64<PaddingFreeSponge<KeccakF, 25, 17, 4>>,
    KeccakCompressionFunction,
    4,
>;

pub(crate) type KeccakStarkConfig<F, EF, DFT> = StarkConfig<
    TwoAdicFriPcs<F, DFT, KeccakMerkleMmcs<F>, ExtensionMmcs<F, EF, KeccakMerkleMmcs<F>>>,
    EF,
    SerializingChallenger32<F, HashChallenger<u8, Keccak256Hash, 32>>,
>;
pub(crate) type KeccakCircleStarkConfig<F, EF> = StarkConfig<
    CirclePcs<F, KeccakMerkleMmcs<F>, ExtensionMmcs<F, EF, KeccakMerkleMmcs<F>>>,
    EF,
    SerializingChallenger32<F, HashChallenger<u8, Keccak256Hash, 32>>,
>;

// Types related to using Poseidon2 in the Merkle tree.
pub(crate) type Poseidon2Sponge<Perm24> = PaddingFreeSponge<Perm24, 24, 16, 8>;
pub(crate) type Poseidon2Compression<Perm16> = TruncatedPermutation<Perm16, 2, 8, 16>;
pub(crate) type Poseidon2MerkleMmcs<F, Perm16, Perm24> = MerkleTreeMmcs<
    <F as Field>::Packing,
    <F as Field>::Packing,
    Poseidon2Sponge<Perm24>,
    Poseidon2Compression<Perm16>,
    8,
>;
pub(crate) type Poseidon2StarkConfig<F, EF, DFT, Perm16, Perm24> = StarkConfig<
    TwoAdicFriPcs<
        F,
        DFT,
        Poseidon2MerkleMmcs<F, Perm16, Perm24>,
        ExtensionMmcs<F, EF, Poseidon2MerkleMmcs<F, Perm16, Perm24>>,
    >,
    EF,
    DuplexChallenger<F, Perm24, 24, 16>,
>;
pub(crate) type Poseidon2CircleStarkConfig<F, EF, Perm16, Perm24> = StarkConfig<
    CirclePcs<
        F,
        Poseidon2MerkleMmcs<F, Perm16, Perm24>,
        ExtensionMmcs<F, EF, Poseidon2MerkleMmcs<F, Perm16, Perm24>>,
    >,
    EF,
    DuplexChallenger<F, Perm24, 24, 16>,
>;
