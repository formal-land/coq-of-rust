use alloc::vec;

use p3_field::TwoAdicField;
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_util::log2_strict_usize;

use crate::TwoAdicSubgroupDft;

#[derive(Default, Clone, Debug)]
pub struct NaiveDft;

impl<F: TwoAdicField> TwoAdicSubgroupDft<F> for NaiveDft {
    type Evaluations = RowMajorMatrix<F>;
    fn dft_batch(&self, mat: RowMajorMatrix<F>) -> RowMajorMatrix<F> {
        let w = mat.width();
        let h = mat.height();
        let log_h = log2_strict_usize(h);
        let g = F::two_adic_generator(log_h);

        let mut res = RowMajorMatrix::new(vec![F::ZERO; w * h], w);
        for (res_r, point) in g.powers().take(h).enumerate() {
            for (src_r, point_power) in point.powers().take(h).enumerate() {
                for c in 0..w {
                    res.values[res_r * w + c] += point_power * mat.values[src_r * w + c]
                }
            }
        }

        res
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use p3_baby_bear::BabyBear;
    use p3_field::{Field, PrimeCharacteristicRing};
    use p3_goldilocks::Goldilocks;
    use p3_matrix::dense::RowMajorMatrix;
    use rand::SeedableRng;
    use rand::rngs::SmallRng;

    use crate::{NaiveDft, TwoAdicSubgroupDft};

    #[test]
    fn basic() {
        type F = BabyBear;

        // A few polynomials:
        // 5 + 4x
        // 2 + 3x
        // 0
        let mat = RowMajorMatrix::new(
            vec![
                F::from_u8(5),
                F::from_u8(2),
                F::ZERO,
                F::from_u8(4),
                F::from_u8(3),
                F::ZERO,
            ],
            3,
        );

        let dft = NaiveDft.dft_batch(mat);
        // Expected evaluations on {1, -1}:
        // 9, 1
        // 5, -1
        // 0, 0
        assert_eq!(
            dft,
            RowMajorMatrix::new(
                vec![
                    F::from_u8(9),
                    F::from_u8(5),
                    F::ZERO,
                    F::ONE,
                    F::NEG_ONE,
                    F::ZERO,
                ],
                3,
            )
        )
    }

    #[test]
    fn dft_idft_consistency() {
        type F = Goldilocks;
        let mut rng = SmallRng::seed_from_u64(1);
        let original = RowMajorMatrix::<F>::rand(&mut rng, 8, 3);
        let dft = NaiveDft.dft_batch(original.clone());
        let idft = NaiveDft.idft_batch(dft);
        assert_eq!(original, idft);
    }

    #[test]
    fn coset_dft_idft_consistency() {
        type F = Goldilocks;
        let generator = F::GENERATOR;
        let mut rng = SmallRng::seed_from_u64(1);
        let original = RowMajorMatrix::<F>::rand(&mut rng, 8, 3);
        let dft = NaiveDft.coset_dft_batch(original.clone(), generator);
        let idft = NaiveDft.coset_idft_batch(dft, generator);
        assert_eq!(original, idft);
    }
}
