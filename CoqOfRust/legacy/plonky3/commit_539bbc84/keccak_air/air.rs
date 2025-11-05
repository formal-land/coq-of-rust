use alloc::vec::Vec;
use core::borrow::Borrow;

use p3_air::utils::{andn, xor, xor3};
use p3_air::{Air, AirBuilder, BaseAir};
use p3_field::{FieldAlgebra, PrimeField64};
use p3_matrix::dense::RowMajorMatrix;
use p3_matrix::Matrix;
use rand::random;

use crate::columns::{KeccakCols, NUM_KECCAK_COLS};
use crate::constants::rc_value_bit;
use crate::round_flags::eval_round_flags;
use crate::{generate_trace_rows, BITS_PER_LIMB, NUM_ROUNDS, U64_LIMBS};

/// Assumes the field size is at least 16 bits.
#[derive(Debug)]
pub struct KeccakAir {}

impl KeccakAir {
    pub fn generate_trace_rows<F: PrimeField64>(
        &self,
        num_hashes: usize,
        extra_capacity_bits: usize,
    ) -> RowMajorMatrix<F> {
        let inputs = (0..num_hashes).map(|_| random()).collect::<Vec<_>>();
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
                for limb in 0..U64_LIMBS {
                    builder
                        .when(first_step)
                        .assert_eq(local.preimage[y][x][limb], local.a[y][x][limb]);
                }
            }
        }

        // If this is not the final step, the local and next preimages must match.
        for y in 0..5 {
            for x in 0..5 {
                for limb in 0..U64_LIMBS {
                    builder
                        .when(not_final_step.clone())
                        .when_transition()
                        .assert_eq(local.preimage[y][x][limb], next.preimage[y][x][limb]);
                }
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
            for z in 0..64 {
                // Check to ensure all entries of C are bools.
                builder.assert_bool(local.c[x][z]);
                let xor = xor3::<AB::Expr>(
                    local.c[x][z].into(),
                    local.c[(x + 4) % 5][z].into(),
                    local.c[(x + 1) % 5][(z + 63) % 64].into(),
                );
                let c_prime = local.c_prime[x][z];
                builder.assert_eq(c_prime, xor);
            }
        }

        // Check that the input limbs are consistent with A' and D.
        // A[x, y, z] = xor(A'[x, y, z], D[x, y, z])
        //            = xor(A'[x, y, z], C[x - 1, z], C[x + 1, z - 1])
        //            = xor(A'[x, y, z], C[x, z], C'[x, z]).
        // The last step is valid based on the identity we checked above.
        // It isn't required, but makes this check a bit cleaner.
        // We also check that all entires of A' are bools.
        // This has the side effect of also range checking the limbs of A.
        for y in 0..5 {
            for x in 0..5 {
                let get_bit = |z| {
                    let a_prime: AB::Var = local.a_prime[y][x][z];
                    let c: AB::Var = local.c[x][z];
                    let c_prime: AB::Var = local.c_prime[x][z];
                    xor3::<AB::Expr>(a_prime.into(), c.into(), c_prime.into())
                };

                for limb in 0..U64_LIMBS {
                    let a_limb = local.a[y][x][limb];
                    let computed_limb = (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB)
                        .rev()
                        .fold(AB::Expr::ZERO, |acc, z| {
                            // Check to ensure all entries of A' are bools.
                            builder.assert_bool(local.a_prime[y][x][z]);
                            acc.double() + get_bit(z)
                        });
                    builder.assert_eq(computed_limb, a_limb);
                }
            }
        }

        // xor_{i=0}^4 A'[x, i, z] = C'[x, z], so for each x, z,
        // diff * (diff - 2) * (diff - 4) = 0, where
        // diff = sum_{i=0}^4 A'[x, i, z] - C'[x, z]
        for x in 0..5 {
            for z in 0..64 {
                let sum: AB::Expr = (0..5).map(|y| local.a_prime[y][x][z].into()).sum();
                let diff = sum - local.c_prime[x][z];
                // This should be slightly faster than from_canonical_u8(4) for some fields.
                let four = AB::Expr::TWO.double();
                builder.assert_zero(diff.clone() * (diff.clone() - AB::Expr::TWO) * (diff - four));
            }
        }

        // A''[x, y] = xor(B[x, y], andn(B[x + 1, y], B[x + 2, y])).
        // As B is a rotation of A', all entries must be bools and so
        // this check also range checks A''.
        for y in 0..5 {
            for x in 0..5 {
                let get_bit = |z| {
                    let andn = andn::<AB::Expr>(
                        local.b((x + 1) % 5, y, z).into(),
                        local.b((x + 2) % 5, y, z).into(),
                    );
                    xor::<AB::Expr>(local.b(x, y, z).into(), andn)
                };

                for limb in 0..U64_LIMBS {
                    let computed_limb = (limb * BITS_PER_LIMB..(limb + 1) * BITS_PER_LIMB)
                        .rev()
                        .fold(AB::Expr::ZERO, |acc, z| acc.double() + get_bit(z));
                    builder.assert_eq(computed_limb, local.a_prime_prime[y][x][limb]);
                }
            }
        }

        // A'''[0, 0] = A''[0, 0] XOR RC
        for limb in 0..U64_LIMBS {
            let computed_a_prime_prime_0_0_limb = (limb * BITS_PER_LIMB
                ..(limb + 1) * BITS_PER_LIMB)
                .rev()
                .fold(AB::Expr::ZERO, |acc, z| {
                    // Check to ensure the bits of A''[0, 0] are boolean.
                    builder.assert_bool(local.a_prime_prime_0_0_bits[z]);
                    acc.double() + local.a_prime_prime_0_0_bits[z]
                });
            let a_prime_prime_0_0_limb = local.a_prime_prime[0][0][limb];
            builder.assert_eq(computed_a_prime_prime_0_0_limb, a_prime_prime_0_0_limb);
        }

        let get_xored_bit = |i| {
            let mut rc_bit_i = AB::Expr::ZERO;
            for r in 0..NUM_ROUNDS {
                let this_round = local.step_flags[r];
                let this_round_constant = AB::Expr::from_bool(rc_value_bit(r, i) != 0);
                rc_bit_i += this_round * this_round_constant;
            }

            xor::<AB::Expr>(local.a_prime_prime_0_0_bits[i].into(), rc_bit_i)
        };

        for limb in 0..U64_LIMBS {
            let a_prime_prime_prime_0_0_limb = local.a_prime_prime_prime_0_0_limbs[limb];
            let computed_a_prime_prime_prime_0_0_limb = (limb * BITS_PER_LIMB
                ..(limb + 1) * BITS_PER_LIMB)
                .rev()
                .fold(AB::Expr::ZERO, |acc, z| acc.double() + get_xored_bit(z));
            builder.assert_eq(
                computed_a_prime_prime_prime_0_0_limb,
                a_prime_prime_prime_0_0_limb,
            );
        }

        // Enforce that this round's output equals the next round's input.
        for x in 0..5 {
            for y in 0..5 {
                for limb in 0..U64_LIMBS {
                    let output = local.a_prime_prime_prime(y, x, limb);
                    let input = next.a[y][x][limb];
                    builder
                        .when_transition()
                        .when(not_final_step.clone())
                        .assert_eq(output, input);
                }
            }
        }
    }
}
