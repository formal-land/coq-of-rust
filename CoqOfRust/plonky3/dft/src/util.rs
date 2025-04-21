use core::borrow::BorrowMut;

use p3_field::{Field, PrimeCharacteristicRing};
use p3_matrix::Matrix;
use p3_matrix::dense::{DenseMatrix, DenseStorage, RowMajorMatrix};
use p3_util::log2_strict_usize;
use tracing::instrument;

/// Divide each coefficient of the given matrix by its height.
///
/// # Panics
///
/// Panics if the height of the matrix is not a power of two.
#[instrument(skip_all, fields(dims = %mat.dimensions()))]
pub fn divide_by_height<F: Field, S: DenseStorage<F> + BorrowMut<[F]>>(
    mat: &mut DenseMatrix<F, S>,
) {
    let h = mat.height();
    let log_h = log2_strict_usize(h);
    // It's cheaper to use div_2exp_u64 as this usually avoids an inversion.
    // It's also cheaper to work in the PrimeSubfield whenever possible.
    let h_inv_subfield = F::PrimeSubfield::ONE.div_2exp_u64(log_h as u64);
    let h_inv = F::from_prime_subfield(h_inv_subfield);
    mat.scale(h_inv)
}

/// Multiply each element of row `i` of `mat` by `shift**i`.
pub(crate) fn coset_shift_cols<F: Field>(mat: &mut RowMajorMatrix<F>, shift: F) {
    mat.rows_mut()
        .zip(shift.powers())
        .for_each(|(row, weight)| {
            row.iter_mut().for_each(|coeff| {
                *coeff *= weight;
            })
        });
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use p3_baby_bear::BabyBear;
    use p3_matrix::dense::RowMajorMatrix;

    use super::*;

    type F = BabyBear;

    #[test]
    fn test_divide_by_height_2x2() {
        // Matrix:
        // [ 2, 4 ]
        // [ 6, 8 ]
        //
        // height = 2 => divide each element by 2
        let mut mat = RowMajorMatrix::new(
            vec![F::from_u8(2), F::from_u8(4), F::from_u8(6), F::from_u8(8)],
            2,
        );

        divide_by_height(&mut mat);

        // Compute: [2, 4, 6, 8] * 1/2 = [1, 2, 3, 4]
        let expected = vec![F::from_u8(1), F::from_u8(2), F::from_u8(3), F::from_u8(4)];

        assert_eq!(mat.values, expected);
    }

    #[test]
    fn test_divide_by_height_1x4() {
        // Matrix:
        // [ 10, 20, 30, 40 ]
        // height = 1 => no division (1⁻¹ = 1), matrix should remain unchanged
        let mut mat = RowMajorMatrix::new_row(vec![
            F::from_u8(10),
            F::from_u8(20),
            F::from_u8(30),
            F::from_u8(40),
        ]);

        divide_by_height(&mut mat);

        let expected = vec![
            F::from_u8(10),
            F::from_u8(20),
            F::from_u8(30),
            F::from_u8(40),
        ];

        assert_eq!(mat.values, expected);
    }

    #[test]
    #[should_panic]
    fn test_divide_by_height_non_power_of_two_height_should_panic() {
        // Matrix of height = 3 is not a power of two → should panic
        let mut mat = RowMajorMatrix::new(vec![F::from_u8(1), F::from_u8(2), F::from_u8(3)], 1);

        divide_by_height(&mut mat);
    }

    #[test]
    fn test_coset_shift_cols_3x2_shift_2() {
        // Input matrix:
        // [ 1, 2 ]
        // [ 3, 4 ]
        // [ 5, 6 ]
        //
        // shift = 2
        // Row 0: shift^0 = 1 → [1 * 1, 2 * 1] = [1, 2]
        // Row 1: shift^1 = 2 → [3 * 2, 4 * 2] = [6, 8]
        // Row 2: shift^2 = 4 → [5 * 4, 6 * 4] = [20, 24]

        let mut mat = RowMajorMatrix::new(
            vec![
                F::from_u8(1),
                F::from_u8(2),
                F::from_u8(3),
                F::from_u8(4),
                F::from_u8(5),
                F::from_u8(6),
            ],
            2,
        );

        coset_shift_cols(&mut mat, F::from_u8(2));

        let expected = vec![
            F::from_u8(1),
            F::from_u8(2),
            F::from_u8(6),
            F::from_u8(8),
            F::from_u8(20),
            F::from_u8(24),
        ];

        assert_eq!(mat.values, expected);
    }

    #[test]
    fn test_coset_shift_cols_identity_shift() {
        // shift = 1 → all weights = 1 → matrix should remain unchanged
        let mut mat = RowMajorMatrix::new(
            vec![F::from_u8(7), F::from_u8(8), F::from_u8(9), F::from_u8(10)],
            2,
        );

        coset_shift_cols(&mut mat, F::from_u8(1));

        let expected = vec![F::from_u8(7), F::from_u8(8), F::from_u8(9), F::from_u8(10)];

        assert_eq!(mat.values, expected);
    }
}
