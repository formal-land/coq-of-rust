//! As the security analysis of Poseidon2 is identical to that of Poseidon,
//! the relevant constraints regarding the number of full/partial rounds required can be found in
//! the original paper: `<https://eprint.iacr.org/2019/458.pdf>` and the associated codebase:
//! `<https://extgit.iaik.tugraz.at/krypto/hadeshash>` (See generate_params_poseidon.sage)
//!
//! These constraints are broken down into 6 equations:
//! statistical, interpolation, Gröbner 1, 2, 3 and
//! an extra constraint coming from the paper `<https://eprint.iacr.org/2023/537.pdf>`.
//!
//! For our parameters (M = 128, p > 2^30, WIDTH = t >= 8, D = alpha < 12),
//! the statistical constraint always simplifies to requiring RF >= 6.
//! Additionally p does not appear in Gröbner 3 or the constraint coming from `<https://eprint.iacr.org/2023/537.pdf>`.
//! The remaining 3 constraints all can be rearranged into the form:
//! F(RF, RP) >= G(p) where G is a function which is non-decreasing with respect to p.
//!
//! Thus, if some tuple (M, p, WIDTH, D, RF, RP) satisfies all constraints, then so will
//! the tuple (M, q, WIDTH, D, RF, RP) for any 2^30 < q < p.
//! Moreover if RF, RP are the "optimal" round numbers (Optimal meaning minimising the number of S-box operations we need to perform)
//! for two tuples (M, p, WIDTH, D) and (M, q, WIDTH, D), then
//! they will also be optimal for (M, r, WIDTH, D) for any q < r < p.
//!
//! We compute the optimal required number of external (full) and internal (partial) rounds using:
//! `<https://github.com/0xPolygonZero/hash-constants/blob/master/calc_round_numbers.py>`
//! Using the above analysis we can conclude that the round numbers are equal
//! for all 31 bit primes and 64 bit primes respectively.

use p3_field::PrimeField64;
use p3_util::relatively_prime_u64;

/// Given a field, a width and an D return the number of full and partial rounds needed to achieve 128 bit security.
///
/// If d is not a valid permutation of the given field or the optimal parameters for that size of prime
/// have not been computed, an error is returned.
pub const fn poseidon2_round_numbers_128<F: PrimeField64>(
    width: usize,
    d: u64,
) -> Result<(usize, usize), &'static str> {
    // Start by checking that d is a valid permutation.
    if !relatively_prime_u64(d, F::ORDER_U64 - 1) {
        return Err("Invalid permutation: gcd(d, F::ORDER_U64 - 1) must be 1");
    }

    // Next compute the number of bits in p.
    let prime_bit_number = F::ORDER_U64.ilog2() + 1;

    match prime_bit_number {
        31 => match (width, d) {
            (16, 3) => Ok((8, 20)),
            (16, 5) => Ok((8, 14)),
            (16, 7) => Ok((8, 13)),
            (16, 9) => Ok((8, 13)),
            (16, 11) => Ok((8, 13)),
            (24, 3) => Ok((8, 23)),
            (24, 5) => Ok((8, 22)),
            (24, 7) => Ok((8, 21)),
            (24, 9) => Ok((8, 21)),
            (24, 11) => Ok((8, 21)),
            _ => Err("The given pair of width and D has not been checked for these fields"),
        },
        64 => match (width, d) {
            (8, 3) => Ok((8, 41)),
            (8, 5) => Ok((8, 27)),
            (8, 7) => Ok((8, 22)),
            (8, 9) => Ok((8, 19)),
            (8, 11) => Ok((8, 17)),
            (12, 3) => Ok((8, 42)),
            (12, 5) => Ok((8, 27)),
            (12, 7) => Ok((8, 22)),
            (12, 9) => Ok((8, 20)),
            (12, 11) => Ok((8, 18)),
            (16, 3) => Ok((8, 42)),
            (16, 5) => Ok((8, 27)),
            (16, 7) => Ok((8, 22)),
            (16, 9) => Ok((8, 20)),
            (16, 11) => Ok((8, 18)),
            _ => Err("The given pair of width and D has not been checked for these fields"),
        },
        _ => Err("The optimal parameters for that size of prime have not been computed."),
    }
}
