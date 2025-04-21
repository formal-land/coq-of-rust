use alloc::vec::Vec;
use core::mem;

use itertools::Itertools;
use p3_field::extension::{Complex, ComplexExtendable};
use p3_field::{batch_multiplicative_inverse, Field};
use p3_util::linear_map::LinearMap;
use tracing::instrument;

use crate::domain::CircleDomain;

#[derive(Debug, Default)]
pub(crate) struct TwiddleCache<F: Field>(
    // (log_n, shift) -> (twiddles, inverse_twiddles)
    #[allow(clippy::type_complexity)]
    LinearMap<(usize, Complex<F>), (Vec<Vec<F>>, Option<Vec<Vec<F>>>)>,
);

impl<F: ComplexExtendable> TwiddleCache<F> {
    pub(crate) fn get_twiddles(
        &mut self,
        log_n: usize,
        shift: Complex<F>,
        inv: bool,
    ) -> &Vec<Vec<F>> {
        let cache = self
            .0
            .get_or_insert_with((log_n, shift), || (compute_twiddles(log_n, shift), None));
        if !inv {
            &cache.0
        } else {
            cache.1.get_or_insert_with(|| {
                cache
                    .0
                    .iter()
                    .map(|xs| batch_multiplicative_inverse(xs))
                    .collect()
            })
        }
    }
}

/// Computes all (non-inverted) twiddles for the FFT over a circle domain of size 2^log_n, for all layers of the FFT.
#[instrument(skip(shift))]
fn compute_twiddles<F: ComplexExtendable>(log_n: usize, shift: Complex<F>) -> Vec<Vec<F>> {
    let size = 1 << (log_n - 1);

    let init_domain = CircleDomain::new(log_n, shift)
        .points()
        .take(size)
        .collect_vec();

    // After the first step we only need the real part.
    let mut working_domain: Vec<_> = init_domain
        .iter()
        .take(size / 2)
        .map(|x| x.real())
        .collect();

    (0..log_n)
        .map(|i| {
            let size = working_domain.len();
            let output = if i == 0 {
                // The twiddles in step one are the inverse imaginary parts.
                init_domain.iter().map(|x| x.imag()).collect_vec()
            } else {
                let new_working_domain = working_domain
                    .iter()
                    .take(size / 2)
                    // When we square a point, the real part changes as x -> 2x^2 - 1.
                    .map(|x| x.square().double() - F::ONE)
                    .collect();
                mem::replace(&mut working_domain, new_working_domain)
            };
            output
        })
        .collect()
}
