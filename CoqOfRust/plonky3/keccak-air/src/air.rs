use alloc::vec::Vec;
use core::array;
use core::borrow::Borrow;

use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_matrix::Matrix;
use p3_matrix::dense::RowMajorMatrix;
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

use crate::columns::{KeccakCols, NUM_KECCAK_COLS};
use crate::constants::rc_value_bit;
use crate::round_flags::eval_round_flags;
use crate::{BITS_PER_LIMB, NUM_ROUNDS, U64_LIMBS, generate_trace_rows};

/// Assumes the field size is at least 16 bits.
#[derive(Debug)]
pub struct KeccakAir {}

impl KeccakAir {
    pub fn generate_trace_rows<F: PrimeField64>(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F> {
        let mut rng = SmallRng::seed_from_u64(1);
        let inputs = (0..num_hashes).map(|_| rng.random()).collect::<Vec<_>>();
        generate_trace_rows(inputs, extra_capacity_bits)
    }
}

impl<F> BaseAir<F> for KeccakAir {
    fn width(&self) -> usize {
        NUM_KECCAK_COLS
    }
}

impl<AB: AirBuilder> Air<AB> for KeccakAir {
    #[inline]
    fn eval(&self, builder: &mut AB) {
        eval_round_flags(builder);

        let main = builder.main();
        let (local, next) = (main.row_slice(0), main.row_slice(1));
        let local: &KeccakCols<AB::Var> = (*local).borrow();
        let next: &KeccakCols<AB::Var> = (*next).borrow();

        let first_step = local.step_flags[0];
        let final_step = local.step_flags[NUM_ROUNDS - 1];
        let not_final_step = AB::Expr::ONE - final_step;

        // If this is the first step, the input A must match the preimage.
        for y in 0..5 {
            for x in 0..5 {
                builder
                    .when(first_step)
                    .assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
                        local.preimage[y][x][limb] - local.a[y][x][limb]
                    }));
            }
        }

        // If this is not the final step, the local and next preimages must match.
        for y in 0..5 {
            for x in 0..5 {
                builder
                    .when(not_final_step.clone())
                    .when_transition()
                    .assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
                        local.preimage[y][x][limb] - next.preimage[y][x][limb]
                    }));
            }
        }

        // The export flag must be 0 or 1.
        builder.assert_bool(local.export);

        // If this is not the final step, the export flag must be off.
        builder
            .when(not_final_step.clone())
            .assert_zero(local.export);

        // C'[x, z] = xor(C[x, z], C[x - 1, z], C[x + 1, z - 1]).
        // Note that if all entries of C are boolean, the arithmetic generalization
        // xor3 function only outputs 0, 1 and so this check also ensures that all
        // entries of C'[x, z] are boolean.
        for x in 0..5 {
            builder.assert_bools(local.c[x]);
            builder.assert_zeros::<64, _>(array::from_fn(|z| {
                let xor = local.c[x][z].into().xor3(
                    &local.c[(x + 4) % 5][z].into(),
                    &local.c[(x + 1) % 5][(z + 63) % 64].into(),
                );
                local.c_prime[x][z] - xor
            }));
        }

        // Check that the input limbs are consistent with A' and D.
        // A[x, y, z] = xor(A'[x, y, z], D[x, y, z])
        //            = xor(A'[x, y, z], C[x - 1, z], C[x + 1, z - 1])
        //            = xor(A'[x, y, z], C[x, z], C'[x, z]).
        // The last step is valid based on the identity we checked above.
        // It isn't required, but makes this check a bit cleaner.
        // We also check that all entries of A' are bools.
        // This has the side effect of also range checking the limbs of A.
        for y in 0..5 {
            for x in 0..5 {
                let get_bit = |z| {
                    Into::<AB::Expr>::into(local.a_prime[y][x][z]).xor3(
                        &Into::<AB::Expr>::into(local.c[x][z]),
                        &Into::<AB::Expr>::into(local.c_prime[x][z]),
                    )
                };

                // Check that all entries of A'[y][x] are boolean.
                builder.assert_bools(local.a_prime[y][x]);

                builder.assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
                    let computed_limb = (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB)
                        .rev()
                        .fold(AB::Expr::ZERO, |acc, z| {
                            // Check to ensure all entries of A' are bools.
                            acc.double() + get_bit(z)
                        });
                    computed_limb - local.a[y][x][limb]
                }));
            }
        }

        // xor_{i=0}^4 A'[x, i, z] = C'[x, z], so for each x, z,
        // diff * (diff - 2) * (diff - 4) = 0, where
        // diff = sum_{i=0}^4 A'[x, i, z] - C'[x, z]
        for x in 0..5 {
            let four = AB::Expr::TWO.double();
            builder.assert_zeros::<64, _>(array::from_fn(|z| {
                let sum: AB::Expr = (0..5).map(|y| local.a_prime[y][x][z].into()).sum();
                let diff = sum - local.c_prime[x][z];
                diff.clone() * (diff.clone() - AB::Expr::TWO) * (diff - four.clone())
            }));
        }

        // A''[x, y] = xor(B[x, y], andn(B[x + 1, y], B[x + 2, y])).
        // As B is a rotation of A', all entries must be bools and so
        // this check also range checks A''.
        for y in 0..5 {
            for x in 0..5 {
                let get_bit = |z| {
                    let andn = local
                        .b((x + 1) % 5, y, z)
                        .into()
                        .andn(&local.b((x + 2) % 5, y, z).into());
                    andn.xor(&local.b(x, y, z).into())
                };
                builder.assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
                    let computed_limb = (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB)
                        .rev()
                        .fold(AB::Expr::ZERO, |acc, z| acc.double() + get_bit(z));
                    computed_limb - local.a_prime_prime[y][x][limb]
                }));
            }
        }

        // A'''[0, 0] = A''[0, 0] XOR RC
        // Check to ensure the bits of A''[0, 0] are boolean.
        builder.assert_bools(local.a_prime_prime_0_0_bits);
        builder.assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
            let computed_a_prime_prime_0_0_limb = (limb * BITS_PER_LIMB
                ..(limb + 1) * BITS_PER_LIMB)
                .rev()
                .fold(AB::Expr::ZERO, |acc, z| {
                    acc.double() + local.a_prime_prime_0_0_bits[z]
                });
            computed_a_prime_prime_0_0_limb - local.a_prime_prime[0][0][limb]
        }));

        let get_xored_bit = |i| {
            let mut rc_bit_i = AB::Expr::ZERO;
            for r in 0..NUM_ROUNDS {
                let this_round = local.step_flags[r];
                let this_round_constant = AB::Expr::from_bool(rc_value_bit(r, i) != 0);
                rc_bit_i += this_round * this_round_constant;
            }

            rc_bit_i.xor(&local.a_prime_prime_0_0_bits[i].into())
        };

        builder.assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
            let computed_a_prime_prime_prime_0_0_limb = (limb * BITS_PER_LIMB
                ..(limb + 1) * BITS_PER_LIMB)
                .rev()
                .fold(AB::Expr::ZERO, |acc, z| acc.double() + get_xored_bit(z));
            computed_a_prime_prime_prime_0_0_limb - local.a_prime_prime_prime_0_0_limbs[limb]
        }));

        // Enforce that this round's output equals the next round's input.
        for x in 0..5 {
            for y in 0..5 {
                builder
                    .when_transition()
                    .when(not_final_step.clone())
                    .assert_zeros::<U64_LIMBS, _>(array::from_fn(|limb| {
                        local.a_prime_prime_prime(y, x, limb) - next.a[y][x][limb]
                    }));
            }
        }
    }
}
