use alloc::vec;
use alloc::vec::Vec;
use core::marker::PhantomData;

use p3_challenger::CanSample;
use p3_dft::TwoAdicSubgroupDft;
use p3_field::coset::TwoAdicMultiplicativeCoset;
use p3_field::{ExtensionField, Field, TwoAdicField};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_util::log2_strict_usize;
use p3_util::zip_eq::zip_eq;
use serde::{Deserialize, Serialize};

use crate::{OpenedValues, Pcs};

/// A trivial PCS: its commitment is simply the coefficients of each poly.
#[derive(Debug)]
pub struct TrivialPcs<Val: TwoAdicField, Dft: TwoAdicSubgroupDft<Val>> {
    pub dft: Dft,
    // degree bound
    pub log_n: usize,
    pub _phantom: PhantomData<Val>,
}

pub fn eval_coeffs_at_pt<F: Field, EF: ExtensionField<F>>(
    coeffs: &RowMajorMatrix<F>,
    x: EF,
) -> Vec<EF> {
    let mut acc = vec![EF::ZERO; coeffs.width()];
    for r in (0..coeffs.height()).rev() {
        let row = coeffs.row_slice(r);
        for (acc_c, row_c) in acc.iter_mut().zip(row.iter()) {
            *acc_c *= x;
            *acc_c += *row_c;
        }
    }
    acc
}

impl<Val, Dft, Challenge, Challenger> Pcs<Challenge, Challenger> for TrivialPcs<Val, Dft>
where
    Val: TwoAdicField,
    Challenge: ExtensionField<Val>,
    Challenger: CanSample<Challenge>,
    Dft: TwoAdicSubgroupDft<Val>,
    Vec<Vec<Val>>: Serialize + for<'de> Deserialize<'de>,
{
    type Domain = TwoAdicMultiplicativeCoset<Val>;
    type Commitment = Vec<Vec<Val>>;
    type ProverData = Vec<RowMajorMatrix<Val>>;
    type EvaluationsOnDomain<'a> = Dft::Evaluations;
    type Proof = ();
    type Error = ();

    fn natural_domain_for_degree(&self, degree: usize) -> Self::Domain {
        // This panics if (and only if) `degree` is not a power of 2 or `degree`
        // > `1 << Val::TWO_ADICITY`.
        TwoAdicMultiplicativeCoset::new(Val::ONE, log2_strict_usize(degree)).unwrap()
    }

    fn commit(
        &self,
        evaluations: Vec<(Self::Domain, RowMajorMatrix<Val>)>,
    ) -> (Self::Commitment, Self::ProverData) {
        let coeffs: Vec<_> = evaluations
            .into_iter()
            .map(|(domain, evals)| {
                let log_domain_size = log2_strict_usize(domain.size());
                // for now, only commit on larger domain than natural
                assert!(log_domain_size >= self.log_n);
                assert_eq!(domain.size(), evals.height());
                // coset_idft_batch
                let mut coeffs = self.dft.idft_batch(evals);
                coeffs
                    .rows_mut()
                    .zip(domain.shift().inverse().powers())
                    .for_each(|(row, weight)| {
                        row.iter_mut().for_each(|coeff| {
                            *coeff *= weight;
                        })
                    });
                coeffs
            })
            .collect();
        (
            coeffs.clone().into_iter().map(|m| m.values).collect(),
            coeffs,
        )
    }

    fn get_evaluations_on_domain<'a>(
        &self,
        prover_data: &'a Self::ProverData,
        idx: usize,
        domain: Self::Domain,
    ) -> Self::EvaluationsOnDomain<'a> {
        let mut coeffs = prover_data[idx].clone();
        assert!(domain.log_size() >= self.log_n);
        coeffs.values.resize(
            coeffs.values.len() << (domain.log_size() - self.log_n),
            Val::ZERO,
        );
        self.dft.coset_dft_batch(coeffs, domain.shift())
    }

    fn open(
        &self,
        // For each round,
        rounds: Vec<(
            &Self::ProverData,
            // for each matrix,
            Vec<
                // points to open
                Vec<Challenge>,
            >,
        )>,
        _challenger: &mut Challenger,
    ) -> (OpenedValues<Challenge>, Self::Proof) {
        (
            rounds
                .into_iter()
                .map(|(coeffs_for_round, points_for_round)| {
                    // ensure that each matrix corresponds to a set of opening points
                    debug_assert_eq!(coeffs_for_round.len(), points_for_round.len());
                    coeffs_for_round
                        .iter()
                        .zip(points_for_round)
                        .map(|(coeffs_for_mat, points_for_mat)| {
                            points_for_mat
                                .into_iter()
                                .map(|pt| eval_coeffs_at_pt(coeffs_for_mat, pt))
                                .collect()
                        })
                        .collect()
                })
                .collect(),
            (),
        )
    }

    // This is a testing function, so we allow panics for convenience.
    #[allow(clippy::panic_in_result_fn)]
    fn verify(
        &self,
        // For each round:
        rounds: Vec<(
            Self::Commitment,
            // for each matrix:
            Vec<(
                // its domain,
                Self::Domain,
                // for each point:
                Vec<(
                    Challenge,
                    // values at this point
                    Vec<Challenge>,
                )>,
            )>,
        )>,
        _proof: &Self::Proof,
        _challenger: &mut Challenger,
    ) -> Result<(), Self::Error> {
        for (comm, round_opening) in rounds {
            for (coeff_vec, (domain, points_and_values)) in zip_eq(comm, round_opening, ())? {
                let width = coeff_vec.len() / domain.size();
                assert_eq!(width * domain.size(), coeff_vec.len());
                let coeffs = RowMajorMatrix::new(coeff_vec, width);
                for (pt, values) in points_and_values {
                    assert_eq!(eval_coeffs_at_pt(&coeffs, pt), values);
                }
            }
        }
        Ok(())
    }
}
