//! Discrete Fourier Transform, in-place, decimation-in-time
//!
//! Straightforward recursive algorithm, "unrolled" up to size 256.
//!
//! Inspired by Bernstein's djbfft: https://cr.yp.to/djbfft.html

extern crate alloc;
use alloc::vec::Vec;

use itertools::izip;
use p3_field::{Field, PackedFieldPow2, PackedValue, PrimeCharacteristicRing};
use p3_util::log2_strict_usize;

use crate::utils::monty_reduce;
use crate::{FieldParameters, MontyField31, TwoAdicData};

#[inline(always)]
fn backward_butterfly<T: PrimeCharacteristicRing + Copy>(x: T, y: T, roots: T) -> (T, T) {
    let t = y * roots;
    (x + t, x - t)
}

#[inline(always)]
fn backward_butterfly_interleaved<const HALF_RADIX: usize, T: PackedFieldPow2>(
    x: T,
    y: T,
    roots: T,
) -> (T, T) {
    let (x, y) = x.interleave(y, HALF_RADIX);
    let (x, y) = backward_butterfly(x, y, roots);
    x.interleave(y, HALF_RADIX)
}

#[inline]
fn backward_pass_packed<T: PackedFieldPow2>(input: &mut [T], roots: &[T::Scalar]) {
    let packed_roots = T::pack_slice(roots);
    let n = input.len();
    let (xs, ys) = unsafe { input.split_at_mut_unchecked(n / 2) };

    izip!(xs, ys, packed_roots)
        .for_each(|(x, y, &roots)| (*x, *y) = backward_butterfly(*x, *y, roots));
}

#[inline]
fn backward_iterative_layer_1<T: PackedFieldPow2>(input: &mut [T], roots: &[T::Scalar]) {
    let packed_roots = T::pack_slice(roots);
    let n = input.len();
    let (top_half, bottom_half) = unsafe { input.split_at_mut_unchecked(n / 2) };
    let (xs, ys) = unsafe { top_half.split_at_mut_unchecked(n / 4) };
    let (zs, ws) = unsafe { bottom_half.split_at_mut_unchecked(n / 4) };

    izip!(xs, ys, zs, ws, packed_roots).for_each(|(x, y, z, w, &root)| {
        (*x, *y) = backward_butterfly(*x, *y, root);
        (*z, *w) = backward_butterfly(*z, *w, root);
    });
}

#[inline]
fn backward_iterative_packed<const HALF_RADIX: usize, T: PackedFieldPow2>(
    input: &mut [T],
    roots: &[T::Scalar],
) {
    // roots[0] == 1
    // roots <-- [1, roots[1], ..., roots[HALF_RADIX-1], 1, roots[1], ...]
    let roots = T::from_fn(|i| roots[i % HALF_RADIX]);

    input.chunks_exact_mut(2).for_each(|pair| {
        let (x, y) = backward_butterfly_interleaved::<HALF_RADIX, _>(pair[0], pair[1], roots);
        pair[0] = x;
        pair[1] = y;
    });
}

#[inline]
fn backward_iterative_packed_radix_2<T: PackedFieldPow2>(input: &mut [T]) {
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
    /// Breadth-first DIT FFT for smallish vectors (must be >= 64)
    #[inline]
    fn backward_iterative_layer(
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
                    .for_each(|(x, y, &root)| (*x, *y) = backward_butterfly(*x, *y, root));
            });
    }

    #[inline]
    fn backward_iterative_packed_radix_16(input: &mut [<Self as Field>::Packing]) {
        // Rather surprisingly, a version similar where the separate
        // loops in each call to backward_iterative_packed() are
        // combined into one, was not only not faster, but was
        // actually a bit slower.

        // Radix 2
        backward_iterative_packed_radix_2(input);

        // Radix 4
        let roots4 = [MP::INV_ROOTS_8.as_ref()[0], MP::INV_ROOTS_8.as_ref()[2]];
        if <Self as Field>::Packing::WIDTH >= 4 {
            backward_iterative_packed::<2, _>(input, &roots4);
        } else {
            Self::backward_iterative_layer(input, &roots4, 2);
        }

        // Radix 8
        if <Self as Field>::Packing::WIDTH >= 8 {
            backward_iterative_packed::<4, _>(input, MP::INV_ROOTS_8.as_ref());
        } else {
            Self::backward_iterative_layer(input, MP::INV_ROOTS_8.as_ref(), 4);
        }

        // Radix 16
        if <Self as Field>::Packing::WIDTH >= 16 {
            backward_iterative_packed::<8, _>(input, MP::INV_ROOTS_16.as_ref());
        } else {
            Self::backward_iterative_layer(input, MP::INV_ROOTS_16.as_ref(), 8);
        }
    }

    fn backward_iterative(packed_input: &mut [<Self as Field>::Packing], root_table: &[Vec<Self>]) {
        assert!(packed_input.len() >= 2);
        let packing_width = <Self as Field>::Packing::WIDTH;
        let n = packed_input.len() * packing_width;
        let lg_n = log2_strict_usize(n);

        // Start loop after doing radix 16 separately. This value is determined by the largest
        // packing width we will encounter, which is 16 at the moment for AVX512. Specifically
        // it is log_2(max{possible packing widths}) = lg(16) = 4.
        const FIRST_LOOP_LAYER: usize = 4;

        // How many layers have we specialised after the main loop
        const NUM_SPECIALISATIONS: usize = 2;

        // Needed to avoid overlap of the 2 specialisations at the start
        // with the radix-16 specialisation at the end of the loop
        assert!(lg_n >= FIRST_LOOP_LAYER + NUM_SPECIALISATIONS);

        Self::backward_iterative_packed_radix_16(packed_input);

        for lg_m in FIRST_LOOP_LAYER..(lg_n - NUM_SPECIALISATIONS) {
            let s = lg_n - lg_m - 1;
            let m = 1 << lg_m;

            let roots = &root_table[s];
            debug_assert_eq!(roots.len(), m);

            Self::backward_iterative_layer(packed_input, roots, m);
        }
        // Specialise the last few iterations; improves performance a little.
        backward_iterative_layer_1(packed_input, &root_table[1]); // lg_m == lg_n - 2, s == 1
        backward_pass_packed(packed_input, &root_table[0]); // lg_m == lg_n - 1, s == 0
    }

    #[inline]
    fn backward_pass(input: &mut [Self], roots: &[Self]) {
        let half_n = input.len() / 2;
        assert_eq!(roots.len(), half_n);

        // Safe because 0 <= half_n < input.len()
        let (xs, ys) = unsafe { input.split_at_mut_unchecked(half_n) };

        let s = xs[0] + ys[0];
        let t = xs[0] - ys[0];
        xs[0] = s;
        ys[0] = t;

        izip!(&mut xs[1..], &mut ys[1..], &roots[1..]).for_each(|(x, y, &root)| {
            (*x, *y) = backward_butterfly(*x, *y, root);
        });
    }

    #[inline(always)]
    fn backward_2(a: &mut [Self]) {
        assert_eq!(a.len(), 2);

        let s = a[0] + a[1];
        let t = a[0] - a[1];
        a[0] = s;
        a[1] = t;
    }

    #[inline(always)]
    fn backward_4(a: &mut [Self]) {
        assert_eq!(a.len(), 4);

        // Read in bit-reversed order
        let a0 = a[0];
        let a2 = a[1];
        let a1 = a[2];
        let a3 = a[3];

        // Expanding the calculation of t3 saves one instruction
        let t1 = MP::PRIME + a1.value - a3.value;
        let t3 = Self::new_monty(monty_reduce::<MP>(
            t1 as u64 * MP::INV_ROOTS_8.as_ref()[2].value as u64,
        ));
        let t5 = a1 + a3;
        let t4 = a0 + a2;
        let t2 = a0 - a2;

        a[0] = t4 + t5;
        a[1] = t2 + t3;
        a[2] = t4 - t5;
        a[3] = t2 - t3;
    }

    #[inline(always)]
    fn backward_8(a: &mut [Self]) {
        assert_eq!(a.len(), 8);

        // Safe because a.len() == 8
        let (a0, a1) = unsafe { a.split_at_mut_unchecked(a.len() / 2) };
        Self::backward_4(a0);
        Self::backward_4(a1);

        Self::backward_pass(a, MP::INV_ROOTS_8.as_ref());
    }

    #[inline(always)]
    fn backward_16(a: &mut [Self]) {
        assert_eq!(a.len(), 16);

        // Safe because a.len() == 16
        let (a0, a1) = unsafe { a.split_at_mut_unchecked(a.len() / 2) };
        Self::backward_8(a0);
        Self::backward_8(a1);

        Self::backward_pass(a, MP::INV_ROOTS_16.as_ref());
    }

    #[inline(always)]
    fn backward_32(a: &mut [Self], root_table: &[Vec<Self>]) {
        assert_eq!(a.len(), 32);

        // Safe because a.len() == 32
        let (a0, a1) = unsafe { a.split_at_mut_unchecked(a.len() / 2) };
        Self::backward_16(a0);
        Self::backward_16(a1);

        Self::backward_pass(a, &root_table[0]);
    }

    /// Assumes `input.len() >= 64`.
    /// current packing widths.
    #[inline]
    fn backward_fft_recur(input: &mut [<Self as Field>::Packing], root_table: &[Vec<Self>]) {
        const ITERATIVE_FFT_THRESHOLD: usize = 1024;

        let n = input.len() * <Self as Field>::Packing::WIDTH;
        if n <= ITERATIVE_FFT_THRESHOLD {
            Self::backward_iterative(input, root_table);
        } else {
            assert_eq!(n, 1 << (root_table.len() + 1));

            // Safe because input.len() > ITERATIVE_FFT_THRESHOLD
            let (a0, a1) = unsafe { input.split_at_mut_unchecked(input.len() / 2) };
            Self::backward_fft_recur(a0, &root_table[1..]);
            Self::backward_fft_recur(a1, &root_table[1..]);

            backward_pass_packed(input, &root_table[0]);
        }
    }

    #[inline]
    pub fn backward_fft(input: &mut [Self], root_table: &[Vec<Self>]) {
        let n = input.len();
        if n == 1 {
            return;
        }

        assert_eq!(n, 1 << (root_table.len() + 1));
        match n {
            32 => Self::backward_32(input, root_table),
            16 => Self::backward_16(input),
            8 => Self::backward_8(input),
            4 => Self::backward_4(input),
            2 => Self::backward_2(input),
            _ => {
                let packed_input = <Self as Field>::Packing::pack_slice_mut(input);
                Self::backward_fft_recur(packed_input, root_table)
            }
        }
    }
}
