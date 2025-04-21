//! Discrete Fourier Transform, in-place, decimation-in-frequency
//!
//! Straightforward recursive algorithm, "unrolled" up to size 256.
//!
//! Inspired by Bernstein's djbfft: https://cr.yp.to/djbfft.html

extern crate alloc;

use alloc::vec::Vec;

use itertools::izip;
use p3_field::{Field, PackedFieldPow2, PackedValue, PrimeCharacteristicRing, TwoAdicField};
use p3_util::log2_strict_usize;

use crate::utils::monty_reduce;
use crate::{FieldParameters, MontyField31, TwoAdicData};

impl<MP: FieldParameters + TwoAdicData> MontyField31<MP> {
    /// Given a field element `gen` of order n where `n = 2^lg_n`,
    /// return a vector of vectors `table` where table[i] is the
    /// vector of twiddle factors for an fft of length n/2^i. The
    /// values g_i^k for k >= i/2 are skipped as these are just the
    /// negatives of the other roots (using g_i^{i/2} = -1).  The
    /// value gen^0 = 1 is included to aid consistency between the
    /// packed and non-packed variants.
    pub fn roots_of_unity_table(n: usize) -> Vec<Vec<Self>> {
        let lg_n = log2_strict_usize(n);
        let generator = Self::two_adic_generator(lg_n);
        let half_n = 1 << (lg_n - 1);
        // nth_roots = [1, g, g^2, g^3, ..., g^{n/2 - 1}]
        let nth_roots: Vec<_> = generator.powers().take(half_n).collect();

        (0..(lg_n - 1))
            .map(|i| nth_roots.iter().step_by(1 << i).copied().collect())
            .collect()
    }
}

#[inline(always)]
fn forward_butterfly<T: PrimeCharacteristicRing + Copy>(x: T, y: T, roots: T) -> (T, T) {
    let t = x - y;
    (x + y, t * roots)
}

#[inline(always)]
fn forward_butterfly_interleaved<const HALF_RADIX: usize, T: PackedFieldPow2>(
    x: T,
    y: T,
    roots: T,
) -> (T, T) {
    let (x, y) = x.interleave(y, HALF_RADIX);
    let (x, y) = forward_butterfly(x, y, roots);
    x.interleave(y, HALF_RADIX)
}

#[inline]
fn forward_pass_packed<T: PackedFieldPow2>(input: &mut [T], roots: &[T::Scalar]) {
    let packed_roots = T::pack_slice(roots);
    let n = input.len();
    let (xs, ys) = unsafe { input.split_at_mut_unchecked(n / 2) };

    izip!(xs, ys, packed_roots)
        .for_each(|(x, y, &roots)| (*x, *y) = forward_butterfly(*x, *y, roots));
}

#[inline]
fn forward_iterative_layer_1<T: PackedFieldPow2>(input: &mut [T], roots: &[T::Scalar]) {
    let packed_roots = T::pack_slice(roots);
    let n = input.len();
    let (top_half, bottom_half) = unsafe { input.split_at_mut_unchecked(n / 2) };
    let (xs, ys) = unsafe { top_half.split_at_mut_unchecked(n / 4) };
    let (zs, ws) = unsafe { bottom_half.split_at_mut_unchecked(n / 4) };

    izip!(xs, ys, zs, ws, packed_roots).for_each(|(x, y, z, w, &root)| {
        (*x, *y) = forward_butterfly(*x, *y, root);
        (*z, *w) = forward_butterfly(*z, *w, root);
    });
}

#[inline]
fn forward_iterative_packed<const HALF_RADIX: usize, T: PackedFieldPow2>(
    input: &mut [T],
    roots: &[T::Scalar],
) {
    // roots[0] == 1
    // roots <-- [1, roots[1], ..., roots[HALF_RADIX-1], 1, roots[1], ...]
    let roots = T::from_fn(|i| roots[i % HALF_RADIX]);

    input.chunks_exact_mut(2).for_each(|pair| {
        let (x, y) = forward_butterfly_interleaved::<HALF_RADIX, _>(pair[0], pair[1], roots);
        pair[0] = x;
        pair[1] = y;
    });
}

#[inline]
fn forward_iterative_packed_radix_2<T: PackedFieldPow2>(input: &mut [T]) {
    input.chunks_exact_mut(2).for_each(|pair| {
        let x = pair[0];
        let y = pair[1];
        let (mut x, y) = x.interleave(y, 1);
        let t = x - y; // roots[0] == 1
        x += y;
        let (x, y) = x.interleave(t, 1);
        pair[0] = x;
        pair[1] = y;
    });
}

impl<MP: FieldParameters + TwoAdicData> MontyField31<MP> {
    #[inline]
    fn forward_iterative_layer(
        packed_input: &mut [<Self as Field>::Packing],
        roots: &[Self],
        m: usize,
    ) {
        debug_assert_eq!(roots.len(), m);
        let packed_roots = <Self as Field>::Packing::pack_slice(roots);

        // lg_m >= 4, so m = 2^lg_m >= 2^4, hence packing_width divides m
        let packed_m = m / <Self as Field>::Packing::WIDTH;
        packed_input
            .chunks_exact_mut(2 * packed_m)
            .for_each(|layer_chunk| {
                let (xs, ys) = unsafe { layer_chunk.split_at_mut_unchecked(packed_m) };

                izip!(xs, ys, packed_roots)
                    .for_each(|(x, y, &root)| (*x, *y) = forward_butterfly(*x, *y, root));
            });
    }

    #[inline]
    fn forward_iterative_packed_radix_16(input: &mut [<Self as Field>::Packing]) {
        // Rather surprisingly, a version similar where the separate
        // loops in each call to forward_iterative_packed() are
        // combined into one, was not only not faster, but was
        // actually a bit slower.

        // Radix 16
        if <Self as Field>::Packing::WIDTH >= 16 {
            forward_iterative_packed::<8, _>(input, MP::ROOTS_16.as_ref());
        } else {
            Self::forward_iterative_layer(input, MP::ROOTS_16.as_ref(), 8);
        }

        // Radix 8
        if <Self as Field>::Packing::WIDTH >= 8 {
            forward_iterative_packed::<4, _>(input, MP::ROOTS_8.as_ref());
        } else {
            Self::forward_iterative_layer(input, MP::ROOTS_8.as_ref(), 4);
        }

        // Radix 4
        let roots4 = [MP::ROOTS_8.as_ref()[0], MP::ROOTS_8.as_ref()[2]];
        if <Self as Field>::Packing::WIDTH >= 4 {
            forward_iterative_packed::<2, _>(input, &roots4);
        } else {
            Self::forward_iterative_layer(input, &roots4, 2);
        }

        // Radix 2
        forward_iterative_packed_radix_2(input);
    }

    /// Breadth-first DIF FFT for smallish vectors (must be >= 64)
    #[inline]
    fn forward_iterative(packed_input: &mut [<Self as Field>::Packing], root_table: &[Vec<Self>]) {
        assert!(packed_input.len() >= 2);
        let packing_width = <Self as Field>::Packing::WIDTH;
        let n = packed_input.len() * packing_width;
        let lg_n = log2_strict_usize(n);

        // Stop loop early to do radix 16 separately. This value is determined by the largest
        // packing width we will encounter, which is 16 at the moment for AVX512. Specifically
        // it is log_2(max{possible packing widths}) = lg(16) = 4.
        const LAST_LOOP_LAYER: usize = 4;

        // How many layers have we specialised before the main loop
        const NUM_SPECIALISATIONS: usize = 2;

        // Needed to avoid overlap of the 2 specialisations at the start
        // with the radix-16 specialisation at the end of the loop
        assert!(lg_n >= LAST_LOOP_LAYER + NUM_SPECIALISATIONS);

        // Specialise the first NUM_SPECIALISATIONS iterations; improves performance a little.
        forward_pass_packed(packed_input, &root_table[0]); // lg_m == lg_n - 1, s == 0
        forward_iterative_layer_1(packed_input, &root_table[1]); // lg_m == lg_n - 2, s == 1

        // loop from lg_n-2 down to 4.
        for lg_m in (LAST_LOOP_LAYER..(lg_n - NUM_SPECIALISATIONS)).rev() {
            let s = lg_n - lg_m - 1;
            let m = 1 << lg_m;

            let roots = &root_table[s];
            debug_assert_eq!(roots.len(), m);

            Self::forward_iterative_layer(packed_input, roots, m);
        }

        // Last 4 layers
        Self::forward_iterative_packed_radix_16(packed_input);
    }

    #[inline(always)]
    fn forward_butterfly(x: Self, y: Self, w: Self) -> (Self, Self) {
        let t = MP::PRIME + x.value - y.value;
        (
            x + y,
            Self::new_monty(monty_reduce::<MP>(t as u64 * w.value as u64)),
        )
    }

    #[inline]
    fn forward_pass(input: &mut [Self], roots: &[Self]) {
        let half_n = input.len() / 2;
        assert_eq!(roots.len(), half_n);

        // Safe because 0 <= half_n < a.len()
        let (xs, ys) = unsafe { input.split_at_mut_unchecked(half_n) };

        let s = xs[0] + ys[0];
        let t = xs[0] - ys[0];
        xs[0] = s;
        ys[0] = t;

        izip!(&mut xs[1..], &mut ys[1..], &roots[1..]).for_each(|(x, y, &root)| {
            (*x, *y) = Self::forward_butterfly(*x, *y, root);
        });
    }

    #[inline(always)]
    fn forward_2(a: &mut [Self]) {
        assert_eq!(a.len(), 2);

        let s = a[0] + a[1];
        let t = a[0] - a[1];
        a[0] = s;
        a[1] = t;
    }

    #[inline(always)]
    fn forward_4(a: &mut [Self]) {
        assert_eq!(a.len(), 4);

        // Expanding the calculation of t3 saves one instruction
        let t1 = MP::PRIME + a[1].value - a[3].value;
        let t3 = Self::new_monty(monty_reduce::<MP>(
            t1 as u64 * MP::ROOTS_8.as_ref()[2].value as u64,
        ));
        let t5 = a[1] + a[3];
        let t4 = a[0] + a[2];
        let t2 = a[0] - a[2];

        // Return in bit-reversed order
        a[0] = t4 + t5;
        a[1] = t4 - t5;
        a[2] = t2 + t3;
        a[3] = t2 - t3;
    }

    #[inline(always)]
    fn forward_8(a: &mut [Self]) {
        assert_eq!(a.len(), 8);

        Self::forward_pass(a, MP::ROOTS_8.as_ref());

        // Safe because a.len() == 8
        let (a0, a1) = unsafe { a.split_at_mut_unchecked(a.len() / 2) };
        Self::forward_4(a0);
        Self::forward_4(a1);
    }

    #[inline(always)]
    fn forward_16(a: &mut [Self]) {
        assert_eq!(a.len(), 16);

        Self::forward_pass(a, MP::ROOTS_16.as_ref());

        // Safe because a.len() == 16
        let (a0, a1) = unsafe { a.split_at_mut_unchecked(a.len() / 2) };
        Self::forward_8(a0);
        Self::forward_8(a1);
    }

    #[inline(always)]
    fn forward_32(a: &mut [Self], root_table: &[Vec<Self>]) {
        assert_eq!(a.len(), 32);

        Self::forward_pass(a, &root_table[0]);

        // Safe because a.len() == 32
        let (a0, a1) = unsafe { a.split_at_mut_unchecked(a.len() / 2) };
        Self::forward_16(a0);
        Self::forward_16(a1);
    }

    /// Assumes `input.len() >= 64`.
    #[inline]
    fn forward_fft_recur(input: &mut [<Self as Field>::Packing], root_table: &[Vec<Self>]) {
        const ITERATIVE_FFT_THRESHOLD: usize = 1024;

        let n = input.len() * <Self as Field>::Packing::WIDTH;
        if n <= ITERATIVE_FFT_THRESHOLD {
            Self::forward_iterative(input, root_table);
        } else {
            assert_eq!(n, 1 << (root_table.len() + 1));
            forward_pass_packed(input, &root_table[0]);

            // Safe because input.len() > ITERATIVE_FFT_THRESHOLD
            let (a0, a1) = unsafe { input.split_at_mut_unchecked(input.len() / 2) };

            Self::forward_fft_recur(a0, &root_table[1..]);
            Self::forward_fft_recur(a1, &root_table[1..]);
        }
    }

    #[inline]
    pub fn forward_fft(input: &mut [Self], root_table: &[Vec<Self>]) {
        let n = input.len();
        if n == 1 {
            return;
        }
        assert_eq!(n, 1 << (root_table.len() + 1));
        match n {
            32 => Self::forward_32(input, root_table),
            16 => Self::forward_16(input),
            8 => Self::forward_8(input),
            4 => Self::forward_4(input),
            2 => Self::forward_2(input),
            _ => {
                let packed_input = <Self as Field>::Packing::pack_slice_mut(input);
                Self::forward_fft_recur(packed_input, root_table)
            }
        }
    }
}
