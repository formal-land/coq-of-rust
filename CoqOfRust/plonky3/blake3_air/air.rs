use alloc::vec::Vec;
use core::borrow::Borrow;

use itertools::izip;
use p3_air::utils::{add2, add3, pack_bits_le, xor_32_shift};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

use crate::columns::{Blake3Cols, NUM_BLAKE3_COLS};
use crate::constants::{BITS_PER_LIMB, IV, permute};
use crate::{Blake3State, FullRound, QuarterRound, generate_trace_rows};

/// Assumes the field size is at least 16 bits.
#[derive(Debug)]
pub struct Blake3Air {}

impl Blake3Air {
    pub fn generate_trace_rows<F: PrimeField64>(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F> {
        let mut rng = SmallRng::seed_from_u64(1);
        let inputs = (0..num_hashes).map(|_| rng.random()).collect::<Vec<_>>();
        generate_trace_rows(inputs, extra_capacity_bits)
    }

    /// Verify that the quarter round function has been correctly computed.
    ///
    /// We assume that the values in a, b, c, d have all been range checked to be
    /// either boolean (for b, d) or < 2^16 (for a, c). This both range checks all x', x''
    /// and auxiliary variables as well as checking the relevant constraints between
    /// them to conclude that the outputs are correct given the inputs.
    fn quarter_round_function<AB: AirBuilder>(
        &self,
        builder: &mut AB,
        trace: &QuarterRound<<AB as AirBuilder>::Var, <AB as AirBuilder>::Expr>,
    ) {
        // We need to pack some bits together to verify the additions.
        // First we verify a' = a + b + m_{2i} mod 2^32
        let b_0_16 = pack_bits_le(trace.b[..BITS_PER_LIMB].iter().copied());
        let b_16_32 = pack_bits_le(trace.b[BITS_PER_LIMB..].iter().copied());

        add3(
            builder,
            trace.a_prime,
            trace.a,
            &[b_0_16, b_16_32],
            trace.m_two_i,
        );

        // Next we verify that d' = (a' ^ d) >> 16 which is equivalently:  a' = d ^ (d' << 16)
        // This also range checks d' and a'.
        xor_32_shift(builder, trace.a_prime, trace.d, trace.d_prime, 16);

        // Next we verify c' = c + d' mod 2^32
        let d_prime_0_16 = pack_bits_le(trace.d_prime[..BITS_PER_LIMB].iter().copied());
        let d_prime_16_32 = pack_bits_le(trace.d_prime[BITS_PER_LIMB..].iter().copied());
        add2(
            builder,
            trace.c_prime,
            trace.c,
            &[d_prime_0_16, d_prime_16_32],
        );

        // Next we verify that b' = (c' ^ b) >> 12 which is equivalently: c' = b ^ (b' << 12)
        // This also range checks b' and c'.
        xor_32_shift(builder, trace.c_prime, trace.b, trace.b_prime, 12);

        // Next we verify a'' = a' + b' + m_{2i + 1} mod 2^32
        let b_prime_0_16 = pack_bits_le(trace.b_prime[..BITS_PER_LIMB].iter().copied());
        let b_prime_16_32 = pack_bits_le(trace.b_prime[BITS_PER_LIMB..].iter().copied());

        add3(
            builder,
            trace.a_output,
            trace.a_prime,
            &[b_prime_0_16, b_prime_16_32],
            trace.m_two_i_plus_one,
        );

        // Next we verify that d'' = (a'' ^ d') << 8 which is equivalently: a'' = d' ^ (d'' << 8)
        // This also range checks d'' and a''.

        xor_32_shift(builder, trace.a_output, trace.d_prime, trace.d_output, 8);

        // Next we verify c'' = c' + d'' mod 2^32
        let d_output_0_16 = pack_bits_le(trace.d_output[..BITS_PER_LIMB].iter().copied());
        let d_output_16_32 = pack_bits_le(trace.d_output[BITS_PER_LIMB..].iter().copied());
        add2(
            builder,
            trace.c_output,
            trace.c_prime,
            &[d_output_0_16, d_output_16_32],
        );

        // Finally we verify that b'' = (c'' ^ b') << 7 which is equivalently: c'' = b' ^ (b'' << 7)
        // This also range checks b'' and c''.
        xor_32_shift(builder, trace.c_output, trace.b_prime, trace.b_output, 7);

        // Assuming all checks pass, a'', b'', c'', d'' are the correct values and have all been range checked.
    }

    /// Given data for a full round, produce the data corresponding to a
    /// single application of the quarter round function on a column.
    const fn full_round_to_column_quarter_round<'a, T: Copy, U>(
        &self,
        input: &'a Blake3State<T>,
        round_data: &'a FullRound<T>,
        m_vector: &'a [[U; 2]; 16],
        index: usize,
    ) -> QuarterRound<'a, T, U> {
        QuarterRound {
            a: &input.row0[index],
            b: &input.row1[index],
            c: &input.row2[index],
            d: &input.row3[index],

            m_two_i: &m_vector[2 * index],

            a_prime: &round_data.state_prime.row0[index],
            b_prime: &round_data.state_prime.row1[index],
            c_prime: &round_data.state_prime.row2[index],
            d_prime: &round_data.state_prime.row3[index],

            m_two_i_plus_one: &m_vector[2 * index + 1],

            a_output: &round_data.state_middle.row0[index],
            b_output: &round_data.state_middle.row1[index],
            c_output: &round_data.state_middle.row2[index],
            d_output: &round_data.state_middle.row3[index],
        }
    }

    /// Given data for a full round, produce the data corresponding to a
    /// single application of the quarter round function on a diagonal.
    const fn full_round_to_diagonal_quarter_round<'a, T: Copy, U>(
        &self,
        round_data: &'a FullRound<T>,
        m_vector: &'a [[U; 2]; 16],
        index: usize,
    ) -> QuarterRound<'a, T, U> {
        QuarterRound {
            a: &round_data.state_middle.row0[index],
            b: &round_data.state_middle.row1[(index + 1) % 4],
            c: &round_data.state_middle.row2[(index + 2) % 4],
            d: &round_data.state_middle.row3[(index + 3) % 4],

            m_two_i: &m_vector[2 * index + 8],

            a_prime: &round_data.state_middle_prime.row0[index],
            b_prime: &round_data.state_middle_prime.row1[(index + 1) % 4],
            c_prime: &round_data.state_middle_prime.row2[(index + 2) % 4],
            d_prime: &round_data.state_middle_prime.row3[(index + 3) % 4],

            m_two_i_plus_one: &m_vector[2 * index + 9],

            a_output: &round_data.state_output.row0[index],
            b_output: &round_data.state_output.row1[(index + 1) % 4],
            c_output: &round_data.state_output.row2[(index + 2) % 4],
            d_output: &round_data.state_output.row3[(index + 3) % 4],
        }
    }

    /// Verify a full round of the Blake-3 permutation.
    fn verify_round<AB: AirBuilder>(
        &self,
        builder: &mut AB,
        input: &Blake3State<AB::Var>,
        round_data: &FullRound<AB::Var>,
        m_vector: &[[AB::Expr; 2]; 16],
    ) {
        // First we mix the columns.

        // The first column quarter round function involves the states in position: 0, 4, 8, 12
        // Along with the two m_vector elements in the 0 and 1 positions.
        let trace_column_0 =
            self.full_round_to_column_quarter_round(input, round_data, m_vector, 0);
        self.quarter_round_function(builder, &trace_column_0);

        // The next column quarter round function involves the states in position: 1, 5, 9, 13
        // Along with the two m_vector elements in the 2 and 3 positions.
        let trace_column_1 =
            self.full_round_to_column_quarter_round(input, round_data, m_vector, 1);
        self.quarter_round_function(builder, &trace_column_1);

        // The next column quarter round function involves the states in position: 2, 6, 10, 14
        // Along with the two m_vector elements in the 4 and 5 positions.
        let trace_column_2 =
            self.full_round_to_column_quarter_round(input, round_data, m_vector, 2);
        self.quarter_round_function(builder, &trace_column_2);

        // The final column quarter round function involves the states in position: 3, 7, 11, 15
        // Along with the two m_vector elements in the 6 and 7 positions.
        let trace_column_3 =
            self.full_round_to_column_quarter_round(input, round_data, m_vector, 3);
        self.quarter_round_function(builder, &trace_column_3);

        // Second we mix the diagonals.

        // The first diagonal quarter round function involves the states in position: 0, 5, 10, 15
        // Along with the two m_vector elements in the 8 and 9 positions.
        let trace_diagonal_0 = self.full_round_to_diagonal_quarter_round(round_data, m_vector, 0);
        self.quarter_round_function(builder, &trace_diagonal_0);

        // The next diagonal quarter round function involves the states in position: 1, 6, 11, 12
        // Along with the two m_vector elements in the 10 and 11 positions.
        let trace_diagonal_1 = self.full_round_to_diagonal_quarter_round(round_data, m_vector, 1);
        self.quarter_round_function(builder, &trace_diagonal_1);

        // The next diagonal quarter round function involves the states in position: 2, 7, 8, 13
        // Along with the two m_vector elements in the 12 and 13 positions.
        let trace_diagonal_2 = self.full_round_to_diagonal_quarter_round(round_data, m_vector, 2);
        self.quarter_round_function(builder, &trace_diagonal_2);

        // The final diagonal quarter round function involves the states in position: 3, 4, 9, 14
        // Along with the two m_vector elements in the 14 and 15 positions.
        let trace_diagonal_3 = self.full_round_to_diagonal_quarter_round(round_data, m_vector, 3);
        self.quarter_round_function(builder, &trace_diagonal_3);
    }
}

impl<F> BaseAir<F> for Blake3Air {
    fn width(&self) -> usize {
        NUM_BLAKE3_COLS
    }
}

impl<AB: AirBuilder> Air<AB> for Blake3Air {
    #[inline]
    fn eval(&self, builder: &mut AB) {
        let main = builder.main();
        let local = main.row_slice(0);
        let local: &Blake3Cols<AB::Var> = (*local).borrow();

        let initial_row_3 = [
            local.counter_low,
            local.counter_hi,
            local.block_len,
            local.flags,
        ];

        // We start by checking that all the initialization inputs are boolean values.
        local
            .inputs
            .iter()
            .chain(local.chaining_values[0].iter())
            .chain(local.chaining_values[1].iter())
            .chain(initial_row_3.iter())
            .for_each(|elem| elem.iter().for_each(|&bool| builder.assert_bool(bool)));

        // Next we ensure that the row0 and row2 for our initial state have been initialized correctly.

        // row0 should contain the packing of the first 4 chaining_values.
        local.chaining_values[0]
            .iter()
            .zip(local.initial_row0)
            .for_each(|(bits, word)| {
                let low_16 = pack_bits_le(bits[..BITS_PER_LIMB].iter().copied());
                let hi_16 = pack_bits_le(bits[BITS_PER_LIMB..].iter().copied());
                builder.assert_eq(low_16, word[0]);
                builder.assert_eq(hi_16, word[1]);
            });

        // row2 should contain the first four constants in IV.
        local
            .initial_row2
            .iter()
            .zip(IV)
            .for_each(|(row_elem, constant)| {
                builder.assert_eq(row_elem[0], AB::Expr::from_u16(constant[0]));
                builder.assert_eq(row_elem[1], AB::Expr::from_u16(constant[1]));
            });

        let mut m_values: [[AB::Expr; 2]; 16] = local.inputs.map(|bits| {
            [
                pack_bits_le(bits[..BITS_PER_LIMB].iter().copied()),
                pack_bits_le(bits[BITS_PER_LIMB..].iter().copied()),
            ]
        });

        let initial_state = Blake3State {
            row0: local.initial_row0,
            row1: local.chaining_values[1],
            row2: local.initial_row2,
            row3: initial_row_3,
        };

        // Now we can move to verifying that each of the seven rounds have been computed correctly.

        // Round 1:
        self.verify_round(builder, &initial_state, &local.full_rounds[0], &m_values);

        // Permute the vector of m_values.
        permute(&mut m_values);

        // Round 2:
        self.verify_round(
            builder,
            &local.full_rounds[0].state_output,
            &local.full_rounds[1],
            &m_values,
        );

        // Permute the vector of m_values.
        permute(&mut m_values);

        // Round 3:
        self.verify_round(
            builder,
            &local.full_rounds[1].state_output,
            &local.full_rounds[2],
            &m_values,
        );

        // Permute the vector of m_values.
        permute(&mut m_values);

        // Round 4:
        self.verify_round(
            builder,
            &local.full_rounds[2].state_output,
            &local.full_rounds[3],
            &m_values,
        );

        // Permute the vector of m_values.
        permute(&mut m_values);

        // Round 5:
        self.verify_round(
            builder,
            &local.full_rounds[3].state_output,
            &local.full_rounds[4],
            &m_values,
        );

        // Permute the vector of m_values.
        permute(&mut m_values);

        // Round 6:
        self.verify_round(
            builder,
            &local.full_rounds[4].state_output,
            &local.full_rounds[5],
            &m_values,
        );

        // Permute the vector of m_values.
        permute(&mut m_values);

        // Round 7:
        self.verify_round(
            builder,
            &local.full_rounds[5].state_output,
            &local.full_rounds[6],
            &m_values,
        );

        // Verify the final set of xor's.
        // For the first 8 of these we xor state[i] and state[i + 8] (i = 0, .., 7)

        // When i = 0, 1, 2, 3 both inputs are given as 16 bit integers. Hence we need to get the individual bits
        // of one of them in order to test this.

        local
            .final_round_helpers
            .iter()
            .zip(local.full_rounds[6].state_output.row2)
            .for_each(|(bits, word)| {
                let low_16 = pack_bits_le(bits[..BITS_PER_LIMB].iter().copied());
                let hi_16 = pack_bits_le(bits[BITS_PER_LIMB..].iter().copied());
                builder.assert_eq(low_16, word[0]);
                builder.assert_eq(hi_16, word[1]);
            });
        // Additionally, we need to ensure that both local.final_round_helpers and local.outputs[0] are boolean.

        local
            .final_round_helpers
            .iter()
            .chain(local.outputs[0].iter())
            .for_each(|bits| bits.iter().for_each(|&bit| builder.assert_bool(bit)));

        // Finally we check the xor by xor'ing the output with final_round_helpers, packing the bits
        // and comparing with the words in local.full_rounds[6].state_output.row0.

        for (out_bits, left_words, right_bits) in izip!(
            local.outputs[0],
            local.full_rounds[6].state_output.row0,
            local.final_round_helpers
        ) {
            // We can reuse xor_32_shift with a shift of 0.
            // As a = b ^ c if and only if b = a ^ c we can perform our xor on the
            // elements which we have the bits of and then check against a.
            xor_32_shift(builder, &left_words, &out_bits, &right_bits, 0)
        }

        // When i = 4, 5, 6, 7 we already have the bits of state[i] and state[i + 8] making this easy.
        // This check also ensures that local.outputs[1] contains only boolean values.

        for (out_bits, left_bits, right_bits) in izip!(
            local.outputs[1],
            local.full_rounds[6].state_output.row1,
            local.full_rounds[6].state_output.row3
        ) {
            for (out_bit, left_bit, right_bit) in izip!(out_bits, left_bits, right_bits) {
                builder.assert_eq(out_bit, left_bit.into().xor(&right_bit.into()));
            }
        }

        // For the remaining 8, we xor state[i] and chaining_value[i - 8] (i = 8, .., 15)

        // When i = 8, 9, 10, 11, we have the bits state[i] already as we used then in the
        // i = 0, 1, 2, 3 case. Additionally we also have the bits of chaining_value[i - 8].
        // Hence we can directly check that the output is correct.

        for (out_bits, left_bits, right_bits) in izip!(
            local.outputs[2],
            local.chaining_values[0],
            local.final_round_helpers
        ) {
            for (out_bit, left_bit, right_bit) in izip!(out_bits, left_bits, right_bits) {
                builder.assert_eq(out_bit, left_bit.into().xor(&right_bit.into()));
            }
        }

        // This is easy when i = 12, 13, 14, 15 as we already have the bits.
        // This check also ensures that local.outputs[3] contains only boolean values.

        for (out_bits, left_bits, right_bits) in izip!(
            local.outputs[3],
            local.chaining_values[1],
            local.full_rounds[6].state_output.row3
        ) {
            for (out_bit, left_bit, right_bit) in izip!(out_bits, left_bits, right_bits) {
                builder.assert_eq(out_bit, left_bit.into().xor(&right_bit.into()));
            }
        }
    }
}
