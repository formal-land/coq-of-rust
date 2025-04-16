//! Calculate the convolution of two vectors using a Karatsuba-style
//! decomposition and the CRT.
//!
//! This is not a new idea, but we did have the pleasure of
//! reinventing it independently. Some references:
//! - `<https://cr.yp.to/lineartime/multapps-20080515.pdf>`
//! - `<https://2π.com/23/convolution/>`
//!
//! Given a vector v \in F^N, let v(x) \in F[x] denote the polynomial
//! v_0 + v_1 x + ... + v_{N - 1} x^{N - 1}.  Then w is equal to the
//! convolution v * u if and only if w(x) = v(x)u(x) mod x^N - 1.
//! Additionally, define the negacyclic convolution by w(x) = v(x)u(x)
//! mod x^N + 1.  Using the Chinese remainder theorem we can compute
//! w(x) as
//!     w(x) = 1/2 (w_0(x) + w_1(x)) + x^{N/2}/2 (w_0(x) - w_1(x))
//! where
//!     w_0 = v(x)u(x) mod x^{N/2} - 1
//!     w_1 = v(x)u(x) mod x^{N/2} + 1
//!
//! To compute w_0 and w_1 we first compute
//!                  v_0(x) = v(x) mod x^{N/2} - 1
//!                  v_1(x) = v(x) mod x^{N/2} + 1
//!                  u_0(x) = u(x) mod x^{N/2} - 1
//!                  u_1(x) = u(x) mod x^{N/2} + 1
//!
//! Now w_0 is the convolution of v_0 and u_0 which we can compute
//! recursively.  For w_1 we compute the negacyclic convolution
//! v_1(x)u_1(x) mod x^{N/2} + 1 using Karatsuba.
//!
//! There are 2 possible approaches to applying Karatsuba which mirror
//! the DIT vs DIF approaches to FFT's, the left/right decomposition
//! or the even/odd decomposition. The latter seems to have fewer
//! operations and so it is the one implemented below, though it does
//! require a bit more data manipulation. It works as follows:
//!
//! Define the even v_e and odd v_o parts so that v(x) = (v_e(x^2) + x v_o(x^2)).
//! Then v(x)u(x)
//!    = (v_e(x^2)u_e(x^2) + x^2 v_o(x^2)u_o(x^2))
//!      + x ((v_e(x^2) + v_o(x^2))(u_e(x^2) + u_o(x^2))
//!            - (v_e(x^2)u_e(x^2) + v_o(x^2)u_o(x^2)))
//! This reduces the problem to 3 negacyclic convolutions of size N/2 which
//! can be computed recursively.
//!
//! Of course, for small sizes we just explicitly write out the O(n^2)
//! approach.

use core::ops::{Add, AddAssign, Neg, ShrAssign, Sub, SubAssign};

/// This trait collects the operations needed by `Convolve` below.
///
/// TODO: Think of a better name for this.
pub trait RngElt:
    Add<Output = Self>
    + AddAssign
    + Copy
    + Default
    + Neg<Output = Self>
    + ShrAssign<u32>
    + Sub<Output = Self>
    + SubAssign
{
}

impl RngElt for i64 {}
impl RngElt for i128 {}

/// Template function to perform convolution of vectors.
///
/// Roughly speaking, for a convolution of size `N`, it should be
/// possible to add `N` elements of type `T` without overflowing, and
/// similarly for `U`. Then multiplication via `Self::mul` should
/// produce an element of type `V` which will not overflow after about
/// `N` additions (this is an over-estimate).
///
/// For example usage, see `{mersenne-31,baby-bear,goldilocks}/src/mds.rs`.
///
/// NB: In practice, one of the parameters to the convolution will be
/// constant (the MDS matrix). After inspecting Godbolt output, it
/// seems that the compiler does indeed generate single constants as
/// inputs to the multiplication, rather than doing all that
/// arithmetic on the constant values every time. Note however that,
/// for MDS matrices with large entries (N >= 24), these compile-time
/// generated constants will be about N times bigger than they need to
/// be in principle, which could be a potential avenue for some minor
/// improvements.
///
/// NB: If primitive multiplications are still the bottleneck, a
/// further possibility would be to find an MDS matrix some of whose
/// entries are powers of 2. Then the multiplication can be replaced
/// with a shift, which on most architectures has better throughput
/// and latency, and is issued on different ports (1*p06) to
/// multiplication (1*p1).
pub trait Convolve<F, T: RngElt, U: RngElt, V: RngElt> {
    /// Given an input element, retrieve the corresponding internal
    /// element that will be used in calculations.
    fn read(input: F) -> T;

    /// Given input vectors `lhs` and `rhs`, calculate their dot
    /// product. The result can be reduced with respect to the modulus
    /// (of `F`), but it must have the same lower 10 bits as the dot
    /// product if all inputs are considered integers. See
    /// `monty-31/src/mds.rs::barrett_red_monty31()` for an example
    /// of how this can be implemented in practice.
    fn parity_dot<const N: usize>(lhs: [T; N], rhs: [U; N]) -> V;

    /// Convert an internal element of type `V` back into an external
    /// element.
    fn reduce(z: V) -> F;

    /// Convolve `lhs` and `rhs`.
    ///
    /// The parameter `conv` should be the function in this trait that
    /// corresponds to length `N`.
    #[inline(always)]
    fn apply<const N: usize, C: Fn([T; N], [U; N], &mut [V])>(
        lhs: [F; N],
        rhs: [U; N],
        conv: C,
    ) -> [F; N] {
        let lhs = lhs.map(Self::read);
        let mut output = [V::default(); N];
        conv(lhs, rhs, &mut output);
        output.map(Self::reduce)
    }

    #[inline(always)]
    fn conv3(lhs: [T; 3], rhs: [U; 3], output: &mut [V]) {
        output[0] = Self::parity_dot(lhs, [rhs[0], rhs[2], rhs[1]]);
        output[1] = Self::parity_dot(lhs, [rhs[1], rhs[0], rhs[2]]);
        output[2] = Self::parity_dot(lhs, [rhs[2], rhs[1], rhs[0]]);
    }

    #[inline(always)]
    fn negacyclic_conv3(lhs: [T; 3], rhs: [U; 3], output: &mut [V]) {
        output[0] = Self::parity_dot(lhs, [rhs[0], -rhs[2], -rhs[1]]);
        output[1] = Self::parity_dot(lhs, [rhs[1], rhs[0], -rhs[2]]);
        output[2] = Self::parity_dot(lhs, [rhs[2], rhs[1], rhs[0]]);
    }

    #[inline(always)]
    fn conv4(lhs: [T; 4], rhs: [U; 4], output: &mut [V]) {
        // NB: This is just explicitly implementing
        // conv_n_recursive::<4, 2, _, _>(lhs, rhs, output, Self::conv2, Self::negacyclic_conv2)
        let u_p = [lhs[0] + lhs[2], lhs[1] + lhs[3]];
        let u_m = [lhs[0] - lhs[2], lhs[1] - lhs[3]];
        let v_p = [rhs[0] + rhs[2], rhs[1] + rhs[3]];
        let v_m = [rhs[0] - rhs[2], rhs[1] - rhs[3]];

        output[0] = Self::parity_dot(u_m, [v_m[0], -v_m[1]]);
        output[1] = Self::parity_dot(u_m, [v_m[1], v_m[0]]);
        output[2] = Self::parity_dot(u_p, v_p);
        output[3] = Self::parity_dot(u_p, [v_p[1], v_p[0]]);

        output[0] += output[2];
        output[1] += output[3];

        output[0] >>= 1;
        output[1] >>= 1;

        output[2] -= output[0];
        output[3] -= output[1];
    }

    #[inline(always)]
    fn negacyclic_conv4(lhs: [T; 4], rhs: [U; 4], output: &mut [V]) {
        output[0] = Self::parity_dot(lhs, [rhs[0], -rhs[3], -rhs[2], -rhs[1]]);
        output[1] = Self::parity_dot(lhs, [rhs[1], rhs[0], -rhs[3], -rhs[2]]);
        output[2] = Self::parity_dot(lhs, [rhs[2], rhs[1], rhs[0], -rhs[3]]);
        output[3] = Self::parity_dot(lhs, [rhs[3], rhs[2], rhs[1], rhs[0]]);
    }

    #[inline(always)]
    fn conv6(lhs: [T; 6], rhs: [U; 6], output: &mut [V]) {
        conv_n_recursive::<6, 3, T, U, V, _, _>(
            lhs,
            rhs,
            output,
            Self::conv3,
            Self::negacyclic_conv3,
        )
    }

    #[inline(always)]
    fn negacyclic_conv6(lhs: [T; 6], rhs: [U; 6], output: &mut [V]) {
        negacyclic_conv_n_recursive::<6, 3, T, U, V, _>(lhs, rhs, output, Self::negacyclic_conv3)
    }

    #[inline(always)]
    fn conv8(lhs: [T; 8], rhs: [U; 8], output: &mut [V]) {
        conv_n_recursive::<8, 4, T, U, V, _, _>(
            lhs,
            rhs,
            output,
            Self::conv4,
            Self::negacyclic_conv4,
        )
    }

    #[inline(always)]
    fn negacyclic_conv8(lhs: [T; 8], rhs: [U; 8], output: &mut [V]) {
        negacyclic_conv_n_recursive::<8, 4, T, U, V, _>(lhs, rhs, output, Self::negacyclic_conv4)
    }

    #[inline(always)]
    fn conv12(lhs: [T; 12], rhs: [U; 12], output: &mut [V]) {
        conv_n_recursive::<12, 6, T, U, V, _, _>(
            lhs,
            rhs,
            output,
            Self::conv6,
            Self::negacyclic_conv6,
        )
    }

    #[inline(always)]
    fn negacyclic_conv12(lhs: [T; 12], rhs: [U; 12], output: &mut [V]) {
        negacyclic_conv_n_recursive::<12, 6, T, U, V, _>(lhs, rhs, output, Self::negacyclic_conv6)
    }

    #[inline(always)]
    fn conv16(lhs: [T; 16], rhs: [U; 16], output: &mut [V]) {
        conv_n_recursive::<16, 8, T, U, V, _, _>(
            lhs,
            rhs,
            output,
            Self::conv8,
            Self::negacyclic_conv8,
        )
    }

    #[inline(always)]
    fn negacyclic_conv16(lhs: [T; 16], rhs: [U; 16], output: &mut [V]) {
        negacyclic_conv_n_recursive::<16, 8, T, U, V, _>(lhs, rhs, output, Self::negacyclic_conv8)
    }

    #[inline(always)]
    fn conv24(lhs: [T; 24], rhs: [U; 24], output: &mut [V]) {
        conv_n_recursive::<24, 12, T, U, V, _, _>(
            lhs,
            rhs,
            output,
            Self::conv12,
            Self::negacyclic_conv12,
        )
    }

    #[inline(always)]
    fn conv32(lhs: [T; 32], rhs: [U; 32], output: &mut [V]) {
        conv_n_recursive::<32, 16, T, U, V, _, _>(
            lhs,
            rhs,
            output,
            Self::conv16,
            Self::negacyclic_conv16,
        )
    }

    #[inline(always)]
    fn negacyclic_conv32(lhs: [T; 32], rhs: [U; 32], output: &mut [V]) {
        negacyclic_conv_n_recursive::<32, 16, T, U, V, _>(lhs, rhs, output, Self::negacyclic_conv16)
    }

    #[inline(always)]
    fn conv64(lhs: [T; 64], rhs: [U; 64], output: &mut [V]) {
        conv_n_recursive::<64, 32, T, U, V, _, _>(
            lhs,
            rhs,
            output,
            Self::conv32,
            Self::negacyclic_conv32,
        )
    }
}

/// Compute output(x) = lhs(x)rhs(x) mod x^N - 1.
/// Do this recursively using a convolution and negacyclic convolution of size HALF_N = N/2.
#[inline(always)]
fn conv_n_recursive<const N: usize, const HALF_N: usize, T, U, V, C, NC>(
    lhs: [T; N],
    rhs: [U; N],
    output: &mut [V],
    inner_conv: C,
    inner_negacyclic_conv: NC,
) where
    T: RngElt,
    U: RngElt,
    V: RngElt,
    C: Fn([T; HALF_N], [U; HALF_N], &mut [V]),
    NC: Fn([T; HALF_N], [U; HALF_N], &mut [V]),
{
    debug_assert_eq!(2 * HALF_N, N);
    // NB: The compiler is smart enough not to initialise these arrays.
    let mut lhs_pos = [T::default(); HALF_N]; // lhs_pos = lhs(x) mod x^{N/2} - 1
    let mut lhs_neg = [T::default(); HALF_N]; // lhs_neg = lhs(x) mod x^{N/2} + 1
    let mut rhs_pos = [U::default(); HALF_N]; // rhs_pos = rhs(x) mod x^{N/2} - 1
    let mut rhs_neg = [U::default(); HALF_N]; // rhs_neg = rhs(x) mod x^{N/2} + 1

    for i in 0..HALF_N {
        let s = lhs[i];
        let t = lhs[i + HALF_N];

        lhs_pos[i] = s + t;
        lhs_neg[i] = s - t;

        let s = rhs[i];
        let t = rhs[i + HALF_N];

        rhs_pos[i] = s + t;
        rhs_neg[i] = s - t;
    }

    let (left, right) = output.split_at_mut(HALF_N);

    // left = w1 = lhs(x)rhs(x) mod x^{N/2} + 1
    inner_negacyclic_conv(lhs_neg, rhs_neg, left);

    // right = w0 = lhs(x)rhs(x) mod x^{N/2} - 1
    inner_conv(lhs_pos, rhs_pos, right);

    for i in 0..HALF_N {
        left[i] += right[i]; // w_0 + w_1
        left[i] >>= 1; // (w_0 + w_1)/2
        right[i] -= left[i]; // (w_0 - w_1)/2
    }
}

/// Compute output(x) = lhs(x)rhs(x) mod x^N + 1.
/// Do this recursively using three negacyclic convolutions of size HALF_N = N/2.
#[inline(always)]
fn negacyclic_conv_n_recursive<const N: usize, const HALF_N: usize, T, U, V, NC>(
    lhs: [T; N],
    rhs: [U; N],
    output: &mut [V],
    inner_negacyclic_conv: NC,
) where
    T: RngElt,
    U: RngElt,
    V: RngElt,
    NC: Fn([T; HALF_N], [U; HALF_N], &mut [V]),
{
    debug_assert_eq!(2 * HALF_N, N);
    // NB: The compiler is smart enough not to initialise these arrays.
    let mut lhs_even = [T::default(); HALF_N];
    let mut lhs_odd = [T::default(); HALF_N];
    let mut lhs_sum = [T::default(); HALF_N];
    let mut rhs_even = [U::default(); HALF_N];
    let mut rhs_odd = [U::default(); HALF_N];
    let mut rhs_sum = [U::default(); HALF_N];

    for i in 0..HALF_N {
        let s = lhs[2 * i];
        let t = lhs[2 * i + 1];
        lhs_even[i] = s;
        lhs_odd[i] = t;
        lhs_sum[i] = s + t;

        let s = rhs[2 * i];
        let t = rhs[2 * i + 1];
        rhs_even[i] = s;
        rhs_odd[i] = t;
        rhs_sum[i] = s + t;
    }

    let mut even_s_conv = [V::default(); HALF_N];
    let (left, right) = output.split_at_mut(HALF_N);

    // Recursively compute the size N/2 negacyclic convolutions of
    // the even parts, odd parts, and sums.
    inner_negacyclic_conv(lhs_even, rhs_even, &mut even_s_conv);
    inner_negacyclic_conv(lhs_odd, rhs_odd, left);
    inner_negacyclic_conv(lhs_sum, rhs_sum, right);

    // Adjust so that the correct values are in right and
    // even_s_conv respectively:
    right[0] -= even_s_conv[0] + left[0];
    even_s_conv[0] -= left[HALF_N - 1];

    for i in 1..HALF_N {
        right[i] -= even_s_conv[i] + left[i];
        even_s_conv[i] += left[i - 1];
    }

    // Interleave even_s_conv and right in the output:
    for i in 0..HALF_N {
        output[2 * i] = even_s_conv[i];
        output[2 * i + 1] = output[i + HALF_N];
    }
}
