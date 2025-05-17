use alloc::vec::Vec;
use core::array;
use core::mem::transmute;

use p3_air::utils::{u64_to_16_bit_limbs, u64_to_bits_le};
use p3_field::PrimeField64;
use p3_matrix::dense::RowMajorMatrix;
use p3_maybe_rayon::iter::repeat_n;
use p3_maybe_rayon::prelude::*;
use tracing::instrument;

use crate::columns::{KeccakCols, NUM_KECCAK_COLS};
use crate::{NUM_ROUNDS, R, RC, U64_LIMBS};

// TODO: Take generic iterable
#[instrument(name = "generate Keccak trace", skip_all)]
pub fn generate_trace_rows<F: PrimeField64>(
    inputs: Vec<[u64; 25]>,
    extra_capacity_bits: usize,
) -> RowMajorMatrix<F> {
    let num_rows = (inputs.len() * NUM_ROUNDS).next_power_of_two();
    let trace_length = num_rows * NUM_KECCAK_COLS;

    // We allocate extra_capacity_bits now as this will be needed by the dft.
    let mut long_trace = F::zero_vec(trace_length << extra_capacity_bits);
    long_trace.truncate(trace_length);

    let mut trace = RowMajorMatrix::new(long_trace, NUM_KECCAK_COLS);
    let (prefix, rows, suffix) = unsafe { trace.values.align_to_mut::<KeccakCols<F>>() };
    assert!(prefix.is_empty(), "Alignment should match");
    assert!(suffix.is_empty(), "Alignment should match");
    assert_eq!(rows.len(), num_rows);

    let num_padding_inputs = num_rows.div_ceil(NUM_ROUNDS) - inputs.len();
    let padded_inputs = inputs
        .into_par_iter()
        .chain(repeat_n([0; 25], num_padding_inputs));

    rows.par_chunks_mut(NUM_ROUNDS)
        .zip(padded_inputs)
        .for_each(|(row, input)| {
            generate_trace_rows_for_perm(row, input);
        });

    trace
}

/// `rows` will normally consist of 24 rows, with an exception for the final row.
fn generate_trace_rows_for_perm<F: PrimeField64>(rows: &mut [KeccakCols<F>], input: [u64; 25]) {
    let mut current_state: [[u64; 5]; 5] = unsafe { transmute(input) };

    let initial_state: [[[F; 4]; 5]; 5] =
        array::from_fn(|y| array::from_fn(|x| u64_to_16_bit_limbs(current_state[x][y])));

    // Populate the round input for the first round.
    rows[0].a = initial_state;
    rows[0].preimage = initial_state;

    generate_trace_row_for_round(&mut rows[0], 0, &mut current_state);

    for round in 1..rows.len() {
        rows[round].preimage = initial_state;

        // Copy previous row's output to next row's input.
        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    rows[round].a[y][x][limb] = rows[round - 1].a_prime_prime_prime(y, x, limb);
                }
            }
        }

        generate_trace_row_for_round(&mut rows[round], round, &mut current_state);
    }
}

fn generate_trace_row_for_round<F: PrimeField64>(
    row: &mut KeccakCols<F>,
    round: usize,
    current_state: &mut [[u64; 5]; 5],
) {
    row.step_flags[round] = F::ONE;

    // Populate C[x] = xor(A[x, 0], A[x, 1], A[x, 2], A[x, 3], A[x, 4]).
    let state_c: [u64; 5] = current_state.map(|row| row.iter().fold(0, |acc, y| acc ^ y));
    for (x, elem) in state_c.iter().enumerate() {
        row.c[x] = u64_to_bits_le(*elem);
    }

    // Populate C'[x, z] = xor(C[x, z], C[x - 1, z], C[x + 1, z - 1]).
    let state_c_prime: [u64; 5] =
        array::from_fn(|x| state_c[x] ^ state_c[(x + 4) % 5] ^ state_c[(x + 1) % 5].rotate_left(1));
    for (x, elem) in state_c_prime.iter().enumerate() {
        row.c_prime[x] = u64_to_bits_le(*elem);
    }

    // Populate A'. To avoid shifting indices, we rewrite
    //     A'[x, y, z] = xor(A[x, y, z], C[x - 1, z], C[x + 1, z - 1])
    // as
    //     A'[x, y, z] = xor(A[x, y, z], C[x, z], C'[x, z]).
    *current_state =
        array::from_fn(|i| array::from_fn(|j| current_state[i][j] ^ state_c[i] ^ state_c_prime[i]));
    for (x, x_row) in current_state.iter().enumerate() {
        for (y, elem) in x_row.iter().enumerate() {
            row.a_prime[y][x] = u64_to_bits_le(*elem);
        }
    }

    // Rotate the current state to get the B array.
    *current_state = array::from_fn(|i| {
        array::from_fn(|j| {
            let new_i = (i + 3 * j) % 5;
            let new_j = i;
            current_state[new_i][new_j].rotate_left(R[new_i][new_j] as u32)
        })
    });

    // Populate A''.
    // A''[x, y] = xor(B[x, y], andn(B[x + 1, y], B[x + 2, y])).
    *current_state = array::from_fn(|i| {
        array::from_fn(|j| {
            current_state[i][j] ^ ((!current_state[(i + 1) % 5][j]) & current_state[(i + 2) % 5][j])
        })
    });
    for (x, x_row) in current_state.iter().enumerate() {
        for (y, elem) in x_row.iter().enumerate() {
            row.a_prime_prime[y][x] = u64_to_16_bit_limbs(*elem);
        }
    }

    row.a_prime_prime_0_0_bits = u64_to_bits_le(current_state[0][0]);

    // A''[0, 0] is additionally xor'd with RC.
    current_state[0][0] ^= RC[round];

    row.a_prime_prime_prime_0_0_limbs = u64_to_16_bit_limbs(current_state[0][0]);
}
