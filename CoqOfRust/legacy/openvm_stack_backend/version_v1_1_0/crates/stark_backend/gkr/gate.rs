use p3_field::Field;

use crate::{gkr::types::GkrMask, poly::uni::Fraction};

/// Defines how a circuit operates locally on two input rows to produce a single output row.
/// This local 2-to-1 constraint is what gives the whole circuit its "binary tree" structure.
///
/// Binary tree structured circuits have a highly regular wiring pattern that fit the structure of
/// the circuits defined in [Thaler13] which allow for efficient linear time (linear in size of the
/// circuit) GKR prover implementations.
///
/// [Thaler13]: https://eprint.iacr.org/2013/351.pdf
#[derive(Debug, Clone, Copy)]
pub enum Gate {
    LogUp,
    GrandProduct,
}

impl Gate {
    /// Returns the output after applying the gate to the mask.
    pub(crate) fn eval<F: Field>(
        &self,
        mask: &GkrMask<F>,
    ) -> Result<Vec<F>, InvalidNumMaskColumnsError> {
        Ok(match self {
            Self::LogUp => {
                if mask.columns().len() != 2 {
                    return Err(InvalidNumMaskColumnsError);
                }

                let [numerator_a, numerator_b] = mask.columns()[0];
                let [denominator_a, denominator_b] = mask.columns()[1];

                let a = Fraction::new(numerator_a, denominator_a);
                let b = Fraction::new(numerator_b, denominator_b);
                let res = a + b;

                vec![res.numerator, res.denominator]
            }
            Self::GrandProduct => {
                if mask.columns().len() != 1 {
                    return Err(InvalidNumMaskColumnsError);
                }

                let [a, b] = mask.columns()[0];
                vec![a * b]
            }
        })
    }
}

/// Error indicating the mask has an invalid number of columns for a gate's operation.
#[derive(Debug)]
pub struct InvalidNumMaskColumnsError;
