use p3_dft::{NaiveDft, TwoAdicSubgroupDft};
use p3_field::{ExtensionField, TwoAdicField};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use rand::SeedableRng;
use rand::distr::{Distribution, StandardUniform};
use rand::rngs::SmallRng;

pub fn test_dft_matches_naive<F, Dft>()
where
    F: TwoAdicField,
    StandardUniform: Distribution<F>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<F>::rand(&mut rng, h, 3);
        let dft_naive = NaiveDft.dft_batch(mat.clone());
        let dft_result = dft.dft_batch(mat);
        assert_eq!(dft_naive, dft_result.to_row_major_matrix());
    }
}

pub fn test_coset_dft_matches_naive<F, Dft>()
where
    F: TwoAdicField,
    StandardUniform: Distribution<F>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<F>::rand(&mut rng, h, 3);
        let shift = F::GENERATOR;
        let coset_dft_naive = NaiveDft.coset_dft_batch(mat.clone(), shift);
        let coset_dft_result = dft.coset_dft_batch(mat, shift);
        assert_eq!(coset_dft_naive, coset_dft_result.to_row_major_matrix());
    }
}

pub fn test_idft_matches_naive<F, Dft>()
where
    F: TwoAdicField,
    StandardUniform: Distribution<F>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<F>::rand(&mut rng, h, 3);
        let idft_naive = NaiveDft.idft_batch(mat.clone());
        let idft_result = dft.idft_batch(mat.clone());
        assert_eq!(idft_naive, idft_result.to_row_major_matrix());
    }
}

pub fn test_coset_idft_matches_naive<F, Dft>()
where
    F: TwoAdicField,
    StandardUniform: Distribution<F>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<F>::rand(&mut rng, h, 3);
        let shift = F::GENERATOR;
        let idft_naive = NaiveDft.coset_idft_batch(mat.clone(), shift);
        let idft_result = dft.coset_idft_batch(mat, shift);
        assert_eq!(idft_naive, idft_result.to_row_major_matrix());
    }
}

pub fn test_lde_matches_naive<F, Dft>()
where
    F: TwoAdicField,
    StandardUniform: Distribution<F>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<F>::rand(&mut rng, h, 3);
        let lde_naive = NaiveDft.lde_batch(mat.clone(), 1);
        let lde_result = dft.lde_batch(mat, 1);
        assert_eq!(lde_naive, lde_result.to_row_major_matrix());
    }
}

pub fn test_coset_lde_matches_naive<F, Dft>()
where
    F: TwoAdicField,
    StandardUniform: Distribution<F>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<F>::rand(&mut rng, h, 3);
        let shift = F::GENERATOR;
        let coset_lde_naive = NaiveDft.coset_lde_batch(mat.clone(), 1, shift);
        let coset_lde_result = dft.coset_lde_batch(mat, 1, shift);
        assert_eq!(coset_lde_naive, coset_lde_result.to_row_major_matrix());
    }
}

pub fn test_dft_idft_consistency<F, Dft>()
where
    F: TwoAdicField,
    StandardUniform: Distribution<F>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let original = RowMajorMatrix::<F>::rand(&mut rng, h, 3);
        let dft_output = dft.dft_batch(original.clone());
        let idft_output = dft.idft_batch(dft_output.to_row_major_matrix());
        assert_eq!(original, idft_output.to_row_major_matrix());
    }
}

pub fn test_dft_algebra_matches_naive<F, EF, Dft>()
where
    F: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField,
    StandardUniform: Distribution<EF>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<EF>::rand(&mut rng, h, 3);
        let dft_naive = NaiveDft.dft_batch(mat.clone());
        let dft_result = dft.dft_algebra_batch(mat);
        assert_eq!(dft_naive, dft_result.to_row_major_matrix());
    }
}

pub fn test_coset_dft_algebra_matches_naive<F, EF, Dft>()
where
    F: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField,
    StandardUniform: Distribution<EF>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<EF>::rand(&mut rng, h, 3);
        let shift = F::GENERATOR;
        let coset_dft_naive = NaiveDft.coset_dft_batch(mat.clone(), EF::from(shift));
        let coset_dft_result = dft.coset_dft_algebra_batch(mat, shift);
        assert_eq!(coset_dft_naive, coset_dft_result.to_row_major_matrix());
    }
}

pub fn test_idft_algebra_matches_naive<F, EF, Dft>()
where
    F: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField,
    StandardUniform: Distribution<EF>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<EF>::rand(&mut rng, h, 3);
        let idft_naive = NaiveDft.idft_batch(mat.clone());
        let idft_result = dft.idft_algebra_batch(mat.clone());
        assert_eq!(idft_naive, idft_result.to_row_major_matrix());
    }
}

pub fn test_coset_idft_algebra_matches_naive<F, EF, Dft>()
where
    F: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField,
    StandardUniform: Distribution<EF>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<EF>::rand(&mut rng, h, 3);
        let shift = F::GENERATOR;
        let idft_naive = NaiveDft.coset_idft_batch(mat.clone(), EF::from(shift));
        let idft_result = dft.coset_idft_algebra_batch(mat, shift);
        assert_eq!(idft_naive, idft_result.to_row_major_matrix());
    }
}

pub fn test_lde_algebra_matches_naive<F, EF, Dft>()
where
    F: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField,
    StandardUniform: Distribution<EF>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<EF>::rand(&mut rng, h, 3);
        let lde_naive = NaiveDft.lde_batch(mat.clone(), 1);
        let lde_result = dft.lde_algebra_batch(mat, 1);
        assert_eq!(lde_naive, lde_result.to_row_major_matrix());
    }
}

pub fn test_coset_lde_algebra_matches_naive<F, EF, Dft>()
where
    F: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField,
    StandardUniform: Distribution<EF>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let mat = RowMajorMatrix::<EF>::rand(&mut rng, h, 3);
        let shift = F::GENERATOR;
        let coset_lde_naive = NaiveDft.coset_lde_batch(mat.clone(), 1, EF::from(shift));
        let coset_lde_result = dft.coset_lde_algebra_batch(mat, 1, shift);
        assert_eq!(coset_lde_naive, coset_lde_result.to_row_major_matrix());
    }
}

pub fn test_dft_idft_algebra_consistency<F, EF, Dft>()
where
    F: TwoAdicField,
    EF: ExtensionField<F> + TwoAdicField,
    StandardUniform: Distribution<EF>,
    Dft: TwoAdicSubgroupDft<F>,
{
    let dft = Dft::default();
    let mut rng = SmallRng::seed_from_u64(1);
    for log_h in 0..5 {
        let h = 1 << log_h;
        let original = RowMajorMatrix::<EF>::rand(&mut rng, h, 3);
        let dft_output = dft.dft_algebra_batch(original.clone());
        let idft_output = dft.idft_algebra_batch(dft_output.to_row_major_matrix());
        assert_eq!(original, idft_output.to_row_major_matrix());
    }
}

#[macro_export]
macro_rules! test_field_dft {
    ($mod:ident, $field:ty, $extfield:ty, $dft:ty) => {
        mod $mod {
            #[test]
            fn dft_matches_naive() {
                $crate::test_dft_matches_naive::<$field, $dft>();
            }

            #[test]
            fn coset_dft_matches_naive() {
                $crate::test_coset_dft_matches_naive::<$field, $dft>();
            }

            #[test]
            fn idft_matches_naive() {
                $crate::test_idft_matches_naive::<$field, $dft>();
            }

            #[test]
            fn coset_idft_matches_naive() {
                $crate::test_coset_idft_matches_naive::<$field, $dft>();
            }

            #[test]
            fn lde_matches_naive() {
                $crate::test_lde_matches_naive::<$field, $dft>();
            }

            #[test]
            fn coset_lde_matches_naive() {
                $crate::test_coset_lde_matches_naive::<$field, $dft>();
            }

            #[test]
            fn dft_idft_consistency() {
                $crate::test_dft_idft_consistency::<$field, $dft>();
            }

            #[test]
            fn dft_algebra_matches_naive() {
                $crate::test_dft_algebra_matches_naive::<$field, $extfield, $dft>();
            }

            #[test]
            fn coset_dft_algebra_matches_naive() {
                $crate::test_coset_dft_algebra_matches_naive::<$field, $extfield, $dft>();
            }

            #[test]
            fn idft_algebra_matches_naive() {
                $crate::test_idft_algebra_matches_naive::<$field, $extfield, $dft>();
            }

            #[test]
            fn coset_idft_algebra_matches_naive() {
                $crate::test_coset_idft_algebra_matches_naive::<$field, $extfield, $dft>();
            }

            #[test]
            fn lde_algebra_matches_naive() {
                $crate::test_lde_algebra_matches_naive::<$field, $extfield, $dft>();
            }

            #[test]
            fn coset_lde_algebra_matches_naive() {
                $crate::test_coset_lde_algebra_matches_naive::<$field, $extfield, $dft>();
            }

            #[test]
            fn dft_idft_algebra_consistency() {
                $crate::test_dft_idft_algebra_consistency::<$field, $extfield, $dft>();
            }
        }
    };
}
