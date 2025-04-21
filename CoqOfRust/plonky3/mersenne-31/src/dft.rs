//! Implementation of DFT for `Mersenne31`.
//!
//! Strategy follows: `<https://www.robinscheibler.org/2013/02/13/real-fft.html>`
//! In short, fold a Mersenne31 DFT of length n into a Mersenne31Complex DFT
//! of length n/2. Some pre/post-processing is necessary so that the result
//! of the transform behaves as expected wrt the convolution theorem etc.
//!
//! Note that we don't return the final n/2 - 1 elements since we know that
//! the "complex conjugate" of the (n-k)th element equals the kth element.
//! The convolution theorem maintains this relationship and so these final
//! n/2 - 1 elements are essentially redundant.

use alloc::vec::Vec;

use itertools::{Itertools, izip};
use p3_dft::TwoAdicSubgroupDft;
use p3_field::extension::Complex;
use p3_field::{Field, PrimeCharacteristicRing, TwoAdicField};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use p3_util::log2_strict_usize;

use crate::Mersenne31;

type F = Mersenne31;
type C = Complex<Mersenne31>;

/// Given an hxw matrix M = (m_{ij}) where h is even, return an
/// (h/2)xw matrix N whose (k,l) entry is
///
///    Mersenne31Complex(m_{2k,l}, m_{2k+1,l})
///
/// i.e. the even rows become the real parts and the odd rows become
/// the imaginary parts.
///
/// This packing is suitable as input to a Fourier Transform over the
/// domain Mersenne31Complex; it is inverse to `idft_postprocess()`
/// below.
fn dft_preprocess(input: RowMajorMatrix<F>) -> RowMajorMatrix<C> {
    assert!(input.height() % 2 == 0, "input height must be even");
    RowMajorMatrix::new(
        input
            .rows()
            .tuples()
            .flat_map(|(row_0, row_1)| {
                // For each pair of rows in input, convert each
                // two-element column into a Mersenne31Complex
                // treating the first row as the real part and the
                // second row as the imaginary part.
                row_0.zip(row_1).map(|(x, y)| C::new_complex(x, y))
            })
            .collect(),
        input.width(),
    )
}

/// Transform the result of applying the DFT to the packed
/// `Mersenne31` values so that the convolution theorem holds.
///
/// Source: https://www.robinscheibler.org/2013/02/13/real-fft.html
///
/// NB: This function and `idft_preprocess()` are inverses.
fn dft_postprocess(input: RowMajorMatrix<C>) -> RowMajorMatrix<C> {
    let h = input.height();
    let log2_h = log2_strict_usize(h); // checks that h is a power of two

    // NB: The original real matrix had height 2h, hence log2(2h) = log2(h) + 1.
    // omega is a 2h-th root of unity
    let omega = C::two_adic_generator(log2_h + 1);
    let mut omega_j = omega;

    let mut output = Vec::with_capacity((h + 1) * input.width());
    output.extend(input.first_row().map(|x| C::new_real(x.real() + x.imag())));

    for j in 1..h {
        let row = izip!(input.row(j), input.row(h - j)).map(|(x, y)| {
            let even = x + y.conjugate();
            // odd = (x - y.conjugate()) * -i
            let odd = C::new_complex(x.imag() + y.imag(), y.real() - x.real());
            (even + odd * omega_j).halve()
        });
        output.extend(row);
        omega_j *= omega;
    }

    output.extend(input.first_row().map(|x| C::new_real(x.real() - x.imag())));
    debug_assert_eq!(output.len(), (h + 1) * input.width());
    RowMajorMatrix::new(output, input.width())
}

/// Undo the transform of the DFT matrix in `dft_postprocess()` so
/// that the inverse DFT can be applied.
///
/// Source: https://www.robinscheibler.org/2013/02/13/real-fft.html
///
/// NB: This function and `dft_postprocess()` are inverses.
fn idft_preprocess(input: RowMajorMatrix<C>) -> RowMajorMatrix<C> {
    let h = input.height() - 1;
    let log2_h = log2_strict_usize(h); // checks that h is a power of two

    // NB: The original real matrix had length 2h, hence log2(2h) = log2(h) + 1.
    // omega is a 2n-th root of unity
    let omega = C::two_adic_generator(log2_h + 1).inverse();
    let mut omega_j = C::ONE;

    let mut output = Vec::with_capacity(h * input.width());
    // TODO: Specialise j = 0 and j = n (which we know must be real)?
    for j in 0..h {
        let row = izip!(input.row(j), input.row(h - j)).map(|(x, y)| {
            let even = x + y.conjugate();
            // odd = (x - y.conjugate()) * -i
            let odd = C::new_complex(x.imag() + y.imag(), y.real() - x.real());
            (even - odd * omega_j).halve()
        });
        output.extend(row);
        omega_j *= omega;
    }
    RowMajorMatrix::new(output, input.width())
}

/// Given an (h/2)xw matrix M = (m_{kl}) = (a_{kl} + I*b_{kl}) (where
/// I is the imaginary unit), return the hxw matrix N whose (i,j)
/// entry is a_{i/2,j} if i is even and b_{(i-1)/2,j} if i is odd.
///
/// This function is inverse to `dft_preprocess()` above.
fn idft_postprocess(input: RowMajorMatrix<C>) -> RowMajorMatrix<F> {
    // Allocate necessary `Vec`s upfront:
    //   1) The actual output,
    //   2) A temporary buf to store the imaginary parts.
    //      This buf is filled and flushed per row
    //      throughout postprocessing to save on allocations.
    let mut output = Vec::with_capacity(input.width() * input.height() * 2);
    let mut buf = Vec::with_capacity(input.width());

    // Convert each row of input into two rows, the first row
    // having the real parts of the input, the second row
    // having the imaginary parts.
    for row in input.rows() {
        for ext in row {
            output.push(ext.real());
            buf.push(ext.imag());
        }
        output.append(&mut buf);
    }

    RowMajorMatrix::new(output, input.width())
}

/// The DFT for Mersenne31
#[derive(Debug, Default, Clone)]
pub struct Mersenne31Dft;

impl Mersenne31Dft {
    /// Compute the DFT of each column of `mat`.
    ///
    /// NB: The DFT works by packing pairs of `Mersenne31` values into
    /// a `Mersenne31Complex` and doing a (half-length) DFT on the
    /// result. In particular, the type of the result elements are in
    /// the extension field, not the domain field.
    pub fn dft_batch<Dft: TwoAdicSubgroupDft<C>>(mat: RowMajorMatrix<F>) -> RowMajorMatrix<C> {
        let dft = Dft::default();
        dft_postprocess(dft.dft_batch(dft_preprocess(mat)).to_row_major_matrix())
    }

    /// Compute the inverse DFT of each column of `mat`.
    ///
    /// NB: See comment on `dft_batch()` for information on packing.
    pub fn idft_batch<Dft: TwoAdicSubgroupDft<C>>(mat: RowMajorMatrix<C>) -> RowMajorMatrix<F> {
        let dft = Dft::default();
        idft_postprocess(dft.idft_batch(idft_preprocess(mat)))
    }
}

#[cfg(test)]
mod tests {
    use rand::distr::{Distribution, StandardUniform};
    use rand::rngs::SmallRng;
    use rand::{Rng, SeedableRng};

    use super::*;
    use crate::Mersenne31ComplexRadix2Dit;

    type Base = Mersenne31;
    type Dft = Mersenne31ComplexRadix2Dit;

    #[test]
    fn consistency()
    where
        StandardUniform: Distribution<Base>,
    {
        const N: usize = 1 << 12;
        let rng = SmallRng::seed_from_u64(1);
        let input = rng
            .sample_iter(StandardUniform)
            .take(N)
            .collect::<Vec<Base>>();
        let input = RowMajorMatrix::new_col(input);
        let fft_input = Mersenne31Dft::dft_batch::<Dft>(input.clone());
        let output = Mersenne31Dft::idft_batch::<Dft>(fft_input);
        assert_eq!(input, output);
    }

    #[test]
    fn convolution()
    where
        StandardUniform: Distribution<Base>,
    {
        const N: usize = 1 << 6;
        let rng = SmallRng::seed_from_u64(1);
        let v = rng
            .sample_iter(StandardUniform)
            .take(2 * N)
            .collect::<Vec<Base>>();
        let a = RowMajorMatrix::new_col(v[..N].to_vec());
        let b = RowMajorMatrix::new_col(v[N..].to_vec());

        let fft_a = Mersenne31Dft::dft_batch::<Dft>(a.clone());
        let fft_b = Mersenne31Dft::dft_batch::<Dft>(b.clone());

        let fft_c = fft_a
            .values
            .iter()
            .zip(fft_b.values.iter())
            .map(|(&xi, &yi)| xi * yi)
            .collect();
        let fft_c = RowMajorMatrix::new_col(fft_c);

        let c = Mersenne31Dft::idft_batch::<Dft>(fft_c);

        let mut conv = Vec::with_capacity(N);
        for i in 0..N {
            let mut t = Base::ZERO;
            for j in 0..N {
                t += a.values[j] * b.values[(N + i - j) % N];
            }
            conv.push(t);
        }

        assert_eq!(c.values, conv);
    }
}
