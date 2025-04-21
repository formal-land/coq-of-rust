use alloc::vec::Vec;
use core::mem::MaybeUninit;

use p3_field::PrimeField;
use p3_matrix::dense::{RowMajorMatrix, RowMajorMatrixViewMut};
use p3_maybe_rayon::prelude::*;
use p3_poseidon2::GenericPoseidon2LinearLayers;
use tracing::instrument;

use crate::columns::{Poseidon2Cols, num_cols};
use crate::{FullRound, PartialRound, RoundConstants, SBox};

#[instrument(name = "generate vectorized Poseidon2 trace", skip_all)]
pub fn generate_vectorized_trace_rows<
    F: PrimeField,
    LinearLayers: GenericPoseidon2LinearLayers<F, WIDTH>,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
    const VECTOR_LEN: usize,
>(
    inputs: Vec<[F; WIDTH]>,
    round_constants: &RoundConstants<F, WIDTH, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>,
    extra_capacity_bits: usize,
) -> RowMajorMatrix<F> {
    let n = inputs.len();
    assert!(
        n % VECTOR_LEN == 0 && (n / VECTOR_LEN).is_power_of_two(),
        "Callers expected to pad inputs to VECTOR_LEN times a power of two"
    );

    let nrows = n.div_ceil(VECTOR_LEN);
    let ncols = num_cols::<WIDTH, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>()
        * VECTOR_LEN;
    let mut vec = Vec::with_capacity((nrows * ncols) << extra_capacity_bits);
    let trace = &mut vec.spare_capacity_mut()[..nrows * ncols];
    let trace = RowMajorMatrixViewMut::new(trace, ncols);

    let (prefix, perms, suffix) = unsafe {
        trace.values.align_to_mut::<Poseidon2Cols<
            MaybeUninit<F>,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
        >>()
    };
    assert!(prefix.is_empty(), "Alignment should match");
    assert!(suffix.is_empty(), "Alignment should match");
    assert_eq!(perms.len(), n);

    perms.par_iter_mut().zip(inputs).for_each(|(perm, input)| {
        generate_trace_rows_for_perm::<
            F,
            LinearLayers,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
        >(perm, input, round_constants);
    });

    unsafe {
        vec.set_len(nrows * ncols);
    }

    RowMajorMatrix::new(vec, ncols)
}

// TODO: Take generic iterable
#[instrument(name = "generate Poseidon2 trace", skip_all)]
pub fn generate_trace_rows<
    F: PrimeField,
    LinearLayers: GenericPoseidon2LinearLayers<F, WIDTH>,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
>(
    inputs: Vec<[F; WIDTH]>,
    constants: &RoundConstants<F, WIDTH, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>,
    extra_capacity_bits: usize,
) -> RowMajorMatrix<F> {
    let n = inputs.len();
    assert!(
        n.is_power_of_two(),
        "Callers expected to pad inputs to a power of two"
    );

    let ncols = num_cols::<WIDTH, SBOX_DEGREE, SBOX_REGISTERS, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>();
    let mut vec = Vec::with_capacity((n * ncols) << extra_capacity_bits);
    let trace = &mut vec.spare_capacity_mut()[..n * ncols];
    let trace = RowMajorMatrixViewMut::new(trace, ncols);

    let (prefix, perms, suffix) = unsafe {
        trace.values.align_to_mut::<Poseidon2Cols<
            MaybeUninit<F>,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
        >>()
    };
    assert!(prefix.is_empty(), "Alignment should match");
    assert!(suffix.is_empty(), "Alignment should match");
    assert_eq!(perms.len(), n);

    perms.par_iter_mut().zip(inputs).for_each(|(perm, input)| {
        generate_trace_rows_for_perm::<
            F,
            LinearLayers,
            WIDTH,
            SBOX_DEGREE,
            SBOX_REGISTERS,
            HALF_FULL_ROUNDS,
            PARTIAL_ROUNDS,
        >(perm, input, constants);
    });

    unsafe {
        vec.set_len(n * ncols);
    }

    RowMajorMatrix::new(vec, ncols)
}

/// `rows` will normally consist of 24 rows, with an exception for the final row.
fn generate_trace_rows_for_perm<
    F: PrimeField,
    LinearLayers: GenericPoseidon2LinearLayers<F, WIDTH>,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
>(
    perm: &mut Poseidon2Cols<
        MaybeUninit<F>,
        WIDTH,
        SBOX_DEGREE,
        SBOX_REGISTERS,
        HALF_FULL_ROUNDS,
        PARTIAL_ROUNDS,
    >,
    mut state: [F; WIDTH],
    constants: &RoundConstants<F, WIDTH, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>,
) {
    perm.export.write(F::ONE);
    perm.inputs
        .iter_mut()
        .zip(state.iter())
        .for_each(|(input, &x)| {
            input.write(x);
        });

    LinearLayers::external_linear_layer(&mut state);

    for (full_round, constants) in perm
        .beginning_full_rounds
        .iter_mut()
        .zip(&constants.beginning_full_round_constants)
    {
        generate_full_round::<_, LinearLayers, WIDTH, SBOX_DEGREE, SBOX_REGISTERS>(
            &mut state, full_round, constants,
        );
    }

    for (partial_round, constant) in perm
        .partial_rounds
        .iter_mut()
        .zip(&constants.partial_round_constants)
    {
        generate_partial_round::<_, LinearLayers, WIDTH, SBOX_DEGREE, SBOX_REGISTERS>(
            &mut state,
            partial_round,
            *constant,
        );
    }

    for (full_round, constants) in perm
        .ending_full_rounds
        .iter_mut()
        .zip(&constants.ending_full_round_constants)
    {
        generate_full_round::<_, LinearLayers, WIDTH, SBOX_DEGREE, SBOX_REGISTERS>(
            &mut state, full_round, constants,
        );
    }
}

#[inline]
fn generate_full_round<
    F: PrimeField,
    LinearLayers: GenericPoseidon2LinearLayers<F, WIDTH>,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
>(
    state: &mut [F; WIDTH],
    full_round: &mut FullRound<MaybeUninit<F>, WIDTH, SBOX_DEGREE, SBOX_REGISTERS>,
    round_constants: &[F; WIDTH],
) {
    // Combine addition of round constants and S-box application in a single loop
    for ((state_i, const_i), sbox_i) in state
        .iter_mut()
        .zip(round_constants.iter())
        .zip(full_round.sbox.iter_mut())
    {
        *state_i += *const_i;
        generate_sbox(sbox_i, state_i);
    }

    LinearLayers::external_linear_layer(state);
    full_round
        .post
        .iter_mut()
        .zip(*state)
        .for_each(|(post, x)| {
            post.write(x);
        });
}

#[inline]
fn generate_partial_round<
    F: PrimeField,
    LinearLayers: GenericPoseidon2LinearLayers<F, WIDTH>,
    const WIDTH: usize,
    const SBOX_DEGREE: u64,
    const SBOX_REGISTERS: usize,
>(
    state: &mut [F; WIDTH],
    partial_round: &mut PartialRound<MaybeUninit<F>, WIDTH, SBOX_DEGREE, SBOX_REGISTERS>,
    round_constant: F,
) {
    state[0] += round_constant;
    generate_sbox(&mut partial_round.sbox, &mut state[0]);
    partial_round.post_sbox.write(state[0]);
    LinearLayers::internal_linear_layer(state);
}

/// Computes the S-box `x -> x^{DEGREE}` and stores the partial data required to
/// verify the computation.
///
/// # Panics
///
/// This method panics if the number of `REGISTERS` is not chosen optimally for the given
/// `DEGREE` or if the `DEGREE` is not supported by the S-box. The supported degrees are
/// `3`, `5`, `7`, and `11`.
#[inline]
fn generate_sbox<F: PrimeField, const DEGREE: u64, const REGISTERS: usize>(
    sbox: &mut SBox<MaybeUninit<F>, DEGREE, REGISTERS>,
    x: &mut F,
) {
    *x = match (DEGREE, REGISTERS) {
        (3, 0) => x.cube(),
        (5, 0) => x.exp_const_u64::<5>(),
        (7, 0) => x.exp_const_u64::<7>(),
        (5, 1) => {
            let x2 = x.square();
            let x3 = x2 * *x;
            sbox.0[0].write(x3);
            x3 * x2
        }
        (7, 1) => {
            let x3 = x.cube();
            sbox.0[0].write(x3);
            x3 * x3 * *x
        }
        (11, 2) => {
            let x2 = x.square();
            let x3 = x2 * *x;
            let x9 = x3.cube();
            sbox.0[0].write(x3);
            sbox.0[1].write(x9);
            x9 * x2
        }
        _ => panic!(
            "Unexpected (DEGREE, REGISTERS) of ({}, {})",
            DEGREE, REGISTERS
        ),
    }
}
