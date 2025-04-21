use p3_mds::MdsPermutation;
use p3_mds::util::apply_circulant;
use p3_symmetric::Permutation;

use crate::x86_64_avx512::packing::PackedGoldilocksAVX512;
use crate::{
    MATRIX_CIRC_MDS_8_SML_ROW, MATRIX_CIRC_MDS_12_SML_ROW, MATRIX_CIRC_MDS_16_SML_ROW,
    MATRIX_CIRC_MDS_24_GOLDILOCKS, MdsMatrixGoldilocks,
};
const fn convert_array<const N: usize>(arr: [i64; N]) -> [u64; N] {
    let mut result: [u64; N] = [0; N];
    let mut i = 0;
    while i < N {
        result[i] = arr[i] as u64;
        i += 1;
    }
    result
}

impl Permutation<[PackedGoldilocksAVX512; 8]> for MdsMatrixGoldilocks {
    fn permute(&self, input: [PackedGoldilocksAVX512; 8]) -> [PackedGoldilocksAVX512; 8] {
        const MATRIX_CIRC_MDS_8_SML_ROW_U64: [u64; 8] = convert_array(MATRIX_CIRC_MDS_8_SML_ROW);
        apply_circulant(&MATRIX_CIRC_MDS_8_SML_ROW_U64, input)
    }

    fn permute_mut(&self, input: &mut [PackedGoldilocksAVX512; 8]) {
        *input = self.permute(*input);
    }
}

impl MdsPermutation<PackedGoldilocksAVX512, 8> for MdsMatrixGoldilocks {}

impl Permutation<[PackedGoldilocksAVX512; 12]> for MdsMatrixGoldilocks {
    fn permute(&self, input: [PackedGoldilocksAVX512; 12]) -> [PackedGoldilocksAVX512; 12] {
        const MATRIX_CIRC_MDS_12_SML_ROW_U64: [u64; 12] = convert_array(MATRIX_CIRC_MDS_12_SML_ROW);
        apply_circulant(&MATRIX_CIRC_MDS_12_SML_ROW_U64, input)
    }

    fn permute_mut(&self, input: &mut [PackedGoldilocksAVX512; 12]) {
        *input = self.permute(*input);
    }
}

impl MdsPermutation<PackedGoldilocksAVX512, 12> for MdsMatrixGoldilocks {}

impl Permutation<[PackedGoldilocksAVX512; 16]> for MdsMatrixGoldilocks {
    fn permute(&self, input: [PackedGoldilocksAVX512; 16]) -> [PackedGoldilocksAVX512; 16] {
        const MATRIX_CIRC_MDS_16_SML_ROW_U64: [u64; 16] = convert_array(MATRIX_CIRC_MDS_16_SML_ROW);
        apply_circulant(&MATRIX_CIRC_MDS_16_SML_ROW_U64, input)
    }

    fn permute_mut(&self, input: &mut [PackedGoldilocksAVX512; 16]) {
        *input = self.permute(*input);
    }
}

impl MdsPermutation<PackedGoldilocksAVX512, 16> for MdsMatrixGoldilocks {}

impl Permutation<[PackedGoldilocksAVX512; 24]> for MdsMatrixGoldilocks {
    fn permute(&self, input: [PackedGoldilocksAVX512; 24]) -> [PackedGoldilocksAVX512; 24] {
        apply_circulant(&MATRIX_CIRC_MDS_24_GOLDILOCKS, input)
    }

    fn permute_mut(&self, input: &mut [PackedGoldilocksAVX512; 24]) {
        *input = self.permute(*input);
    }
}

impl MdsPermutation<PackedGoldilocksAVX512, 24> for MdsMatrixGoldilocks {}

#[cfg(test)]
mod tests {
    use p3_poseidon::Poseidon;
    use p3_symmetric::Permutation;
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    use crate::{Goldilocks, MdsMatrixGoldilocks, PackedGoldilocksAVX512};

    #[test]
    fn test_avx512_poseidon_width_8() {
        let mut rng = SmallRng::seed_from_u64(1);
        type F = Goldilocks;
        type Perm = Poseidon<F, MdsMatrixGoldilocks, 8, 7>;
        let poseidon = Perm::new_from_rng(4, 22, MdsMatrixGoldilocks, &mut rng);

        let input: [F; 8] = rng.random();

        let mut expected = input;
        poseidon.permute_mut(&mut expected);

        let mut avx2_input = input.map(Into::<PackedGoldilocksAVX512>::into);
        poseidon.permute_mut(&mut avx2_input);

        let avx2_output = avx2_input.map(|x| x.0[0]);
        assert_eq!(avx2_output, expected);
    }

    #[test]
    fn test_avx512_poseidon_width_12() {
        let mut rng = SmallRng::seed_from_u64(1);
        type F = Goldilocks;
        type Perm = Poseidon<F, MdsMatrixGoldilocks, 12, 7>;
        let poseidon = Perm::new_from_rng(4, 22, MdsMatrixGoldilocks, &mut rng);

        let input: [F; 12] = rng.random();

        let mut expected = input;
        poseidon.permute_mut(&mut expected);

        let mut avx2_input = input.map(Into::<PackedGoldilocksAVX512>::into);
        poseidon.permute_mut(&mut avx2_input);

        let avx2_output = avx2_input.map(|x| x.0[0]);
        assert_eq!(avx2_output, expected);
    }

    #[test]
    fn test_avx512_poseidon_width_16() {
        let mut rng = SmallRng::seed_from_u64(1);
        type F = Goldilocks;
        type Perm = Poseidon<F, MdsMatrixGoldilocks, 16, 7>;
        let poseidon = Perm::new_from_rng(4, 22, MdsMatrixGoldilocks, &mut rng);

        let input: [F; 16] = rng.random();

        let mut expected = input;
        poseidon.permute_mut(&mut expected);

        let mut avx2_input = input.map(Into::<PackedGoldilocksAVX512>::into);
        poseidon.permute_mut(&mut avx2_input);

        let avx2_output = avx2_input.map(|x| x.0[0]);
        assert_eq!(avx2_output, expected);
    }

    #[test]
    fn test_avx512_poseidon_width_24() {
        let mut rng = SmallRng::seed_from_u64(1);
        type F = Goldilocks;
        type Perm = Poseidon<F, MdsMatrixGoldilocks, 24, 7>;
        let poseidon = Perm::new_from_rng(4, 22, MdsMatrixGoldilocks, &mut rng);

        let input: [F; 24] = rng.random();

        let mut expected = input;
        poseidon.permute_mut(&mut expected);

        let mut avx2_input = input.map(Into::<PackedGoldilocksAVX512>::into);
        poseidon.permute_mut(&mut avx2_input);

        let avx2_output = avx2_input.map(|x| x.0[0]);
        assert_eq!(avx2_output, expected);
    }
}
