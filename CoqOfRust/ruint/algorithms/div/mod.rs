//! ⚠️ Collection of division algorithms.
//!
//! **Warning.** Most functions in this module are currently not considered part
//! of the stable API and may be changed or removed in future minor releases.
//!
//! All division algorithms also compute the remainder. There is no benefit
//! to splitting the division and remainder into separate functions, since
//! the remainder is always computed as part of the division algorithm.
//!
//! These functions are adapted from algorithms in [MG10] and [K97].
//!
//! [K97]: https://cs.stanford.edu/~knuth/taocp.html
//! [MG10]: https://gmplib.org/~tege/division-paper.pdf

#![allow(clippy::similar_names)] // TODO

mod knuth;
mod reciprocal;
mod small;

pub use self::{
    knuth::{div_nxm, div_nxm_normalized},
    reciprocal::{reciprocal, reciprocal_2, reciprocal_2_mg10, reciprocal_mg10, reciprocal_ref},
    small::{
        div_2x1, div_2x1_mg10, div_2x1_ref, div_3x2, div_3x2_mg10, div_3x2_ref, div_nx1,
        div_nx1_normalized, div_nx2, div_nx2_normalized,
    },
};
use crate::algorithms::DoubleWord;

/// ⚠️ Division with remainder.
///
/// **Warning.** This function is not part of the stable API.
///
/// The quotient is stored in the `numerator` and the remainder is stored
/// in the `divisor`.
///
/// # Algorithm
///
/// It trims zeros from the numerator and divisor then solves the trivial cases
/// directly, or dispatches to the [`div_nx1`], [`div_nx2`] or [`div_nxm`]
/// functions.
///
/// # Panics
///
/// Panics if `divisor` is zero.
#[inline]
pub fn div(numerator: &mut [u64], divisor: &mut [u64]) {
    // Trim most significant zeros from divisor.
    let i = divisor
        .iter()
        .rposition(|&x| x != 0)
        .expect("Divisor is zero");
    let divisor = &mut divisor[..=i];
    debug_assert!(!divisor.is_empty());
    debug_assert!(divisor.last() != Some(&0));

    // Trim zeros from numerator
    let numerator = if let Some(i) = numerator.iter().rposition(|&n| n != 0) {
        &mut numerator[..=i]
    } else {
        // Empty numerator (q, r) = (0,0)
        divisor.fill(0);
        return;
    };
    debug_assert!(!numerator.is_empty());
    debug_assert!(*numerator.last().unwrap() != 0);

    // If numerator is smaller than divisor (q, r) = (0, numerator)
    if numerator.len() < divisor.len() {
        let (remainder, padding) = divisor.split_at_mut(numerator.len());
        remainder.copy_from_slice(numerator);
        padding.fill(0);
        numerator.fill(0);
        return;
    }
    debug_assert!(numerator.len() >= divisor.len());

    // Compute quotient and remainder, branching out to different algorithms.
    if divisor.len() <= 2 {
        if divisor.len() == 1 {
            if numerator.len() == 1 {
                let q = numerator[0] / divisor[0];
                let r = numerator[0] % divisor[0];
                numerator[0] = q;
                divisor[0] = r;
            } else {
                divisor[0] = div_nx1(numerator, divisor[0]);
            }
        } else {
            let d = u128::join(divisor[1], divisor[0]);
            let remainder = div_nx2(numerator, d);
            divisor[0] = remainder.low();
            divisor[1] = remainder.high();
        }
    } else {
        div_nxm(numerator, divisor);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::aliases::U512;

    // Test vectors from <https://github.com/chfast/intx/blob/8b5f4748a7386a9530769893dae26b3273e0ffe2/test/unittests/test_div.cpp#L58>
    // [[numerator, divisor, quotient, remainder]; _]
    const INTX_TESTS: [[U512; 4]; 45] = uint!([
        [2_U512, 1_U512, 2_U512, 0_U512],
        [
            0x10000000000000000_U512,
            2_U512,
            0x8000000000000000_U512,
            0_U512,
        ],
        [
            0x7000000000000000_U512,
            0x8000000000000000_U512,
            0_U512,
            0x7000000000000000_U512,
        ],
        [
            0x8000000000000000_U512,
            0x8000000000000000_U512,
            1_U512,
            0_U512,
        ],
        [
            0x8000000000000001_U512,
            0x8000000000000000_U512,
            1_U512,
            1_U512,
        ],
        [
            0x80000000000000010000000000000000_U512,
            0x80000000000000000000000000000000_U512,
            1_U512,
            0x10000000000000000_U512,
        ],
        [
            0x80000000000000000000000000000000_U512,
            0x80000000000000000000000000000001_U512,
            0_U512,
            0x80000000000000000000000000000000_U512,
        ],
        [
            0x478392145435897052_U512,
            0x111_U512,
            0x430f89ebadad0baa_U512,
            8_U512,
        ],
        [
            0x400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000_U512,
            0x800000000000000000000000000000000000000000000000_U512,
            0x800000000000000000000000000000000000000000000000_U512,
            0_U512,
        ],
        [
            0x80000000000000000000000000000000000000000000000000000000000000000000000000000000_U512,
            0x800000000000000000000000000000000000000000000000_U512,
            0x100000000000000000000000000000000_U512,
            0_U512,
        ],
        [
            0x1e00000000000000000000090000000000000000000000000000000000000000000000000000000000000000000000000000000009000000000000000000_U512,
            0xa_U512,
            0x30000000000000000000000e6666666666666666666666666666666666666666666666666666666666666666666666666666666674ccccccccccccccccc_U512,
            8_U512,
        ],
        [
            0x767676767676767676000000767676767676_U512,
            0x2900760076761e00020076760000000076767676000000_U512,
            0_U512,
            0x767676767676767676000000767676767676_U512,
        ],
        [
            0x12121212121212121212121212121212_U512,
            0x232323232323232323_U512,
            0x83a83a83a83a83_U512,
            0x171729292929292929_U512,
        ],
        [
            0xabc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0abc0_U512,
            0x1c01c01c01c01c01c01c01c01c_U512,
            0x621ed21ed21ed21ed21ed21ed224f40bf40bf40bf40bf40bf40bf46e12de12de12de12de12de12de1900000000000000000_U512,
            0xabc0abc0abc0abc0_U512,
        ],
        [
            0xfffff716b61616160b0b0b2b0b0b0becf4bef50a0df4f48b090b2b0bc60a0a00_U512,
            0xfffff716b61616160b0b0b2b0b230b000008010d0a2b00_U512,
            0xffffffffffffffffff_U512,
            0xfffff7169e17030ac1ff082ed51796090b330cd3143500_U512,
        ],
        [
            0x50beb1c60141a0000dc2b0b0b0b0b0b410a0a0df4f40b090b2b0bc60a0a00_U512,
            0x2000110000000d0a300e750a000000090a0a_U512,
            0x285f437064cd09ff8bc5b7857d_U512,
            0x1fda1c384d86199e14bb4edfc6693042f11e_U512,
        ],
        [
            0x4b00000b41000b0b0b2b0b0b0b0b0b410a0aeff4f40b090b2b0bc60a0a1000_U512,
            0x4b00000b41000b0b0b2b0b0b0b0b0b410a0aeff4f40b0a0a_U512,
            0xffffffffffffff_U512,
            0x4b00000b41000b0b0b2b0b0b0b0b0b400b35fbbafe151a0a_U512,
        ],
        [
            0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee_U512,
            7_U512,
            0x22222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222222_U512,
            0_U512,
        ],
        [
            0xf6376770abd3a36b20394c5664afef1194c801c3f05e42566f085ed24d002bb0_U512,
            0xb368d219438b7f3f_U512,
            0x15f53bce87e9fb63c7c3ab03f6c0ba30d3ecf982fa97cdf0a_U512,
            0x4bfd94dbec31523a_U512,
        ],
        [
            0x0_U512,
            0x10900000000000000000000000000000000000000000000000000_U512,
            0x0_U512,
            0x0_U512,
        ],
        [
            0x77676767676760000000000000001002e000000000000040000000e000000000000007f0000000000000000000000000000000000000000f7000000000000_U512,
            0xfffc000000000000767676240000000000002b05760476000000000000000000767676767600000000000000000000000000000000_U512,
            0x7769450c7b994e65025_U512,
            0x241cb1aa4f67c22ae65c9920bf3bb7ad8280311a887aee8be4054a3e242a5ea9ab35d800f2000000000000000000f7000000000000_U512,
        ],
        [
            0xdffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000001000000000000000000000000008100000000001001_U512,
            0xdffffffffffffffffffffffffffffffffffffffffffff3fffffffffffffffffffffffffffff_U512,
            0xffffffffffffffffffffffffffffffffffedb6db6db6e9_U512,
            0x200000000000000000000000000010000f2492492492ec000000000000080ffedb6db6dc6ea_U512,
        ],
        [
            0xff000000000000000000000000000000000000000400000092767600000000000000000000000081000000000000000000000001020000000000eeffffffffff_U512,
            0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000005000000000000000000ffffffffff100000000000000000_U512,
            0x0_U512,
            0xff000000000000000000000000000000000000000400000092767600000000000000000000000081000000000000000000000001020000000000eeffffffffff_U512,
        ],
        [
            0xfffffffffffffffffffffffffffffffffffffffbffffff6d8989ffffffffffffffffffffffff7efffffffffffffffffffffffefdffffffffff110000000001_U512,
            0xfffffffffffffffffffffffaffffffffffffffffff0000000000f00000000000000000_U512,
            0x1000000000000000000000004fffffffffffffffc00ffff8689890fff_U512,
            0xffffffec09fffda0afa81efafc00ffff868d481fff71de0d8100efffff110000000001_U512,
        ],
        [
            0x767676767676000000000076000000000000005600000000000000000000_U512,
            0x767676767676000000000076000000760000_U512,
            0xffffffffffffffffffffffff_U512,
            0x767676007676005600000076000000760000_U512,
        ],
        [
            0x8200000000000000000000000000000000000000000000000000000000000000_U512,
            0x8200000000000000fe000004000000ffff000000fffff700_U512,
            0xfffffffffffffffe_U512,
            0x5fffffbffffff01fd00000700000afffe000001ffffee00_U512,
        ],
        [
            0xdac7fff9ffd9e1322626262626262600_U512,
            0xd021262626262626_U512,
            0x10d1a094108c5da55_U512,
            0x6f386ccc73c11f62_U512,
        ],
        [
            0x8000000000000001800000000000000080000000000000008000000000000000_U512,
            0x800000000000000080000000000000008000000000000000_U512,
            0x10000000000000001_U512,
            0x7fffffffffffffff80000000000000000000000000000000_U512,
        ],
        [
            0x00e8e8e8e2000100000009ea02000000000000ff3ffffff800000010002200000000000000000000000000000000000000000000000000000000000000000000_U512,
            0x00e8e8e8e2000100000009ea02000000000000ff3ffffff800000010002280ff0000000000000000000000000000000000000000000000000000000000000000_U512,
            0_U512,
            0x00e8e8e8e2000100000009ea02000000000000ff3ffffff800000010002200000000000000000000000000000000000000000000000000000000000000000000_U512,
        ],
        [
            0x000000c9700000000000000000023f00c00014ff0000000000000000223008050000000000000000000000000000000000000000000000000000000000000000_U512,
            0x00000000c9700000000000000000023f00c00014ff002c0000000000002231080000000000000000000000000000000000000000000000000000000000000000_U512,
            0xff_U512,
            0x00000000c9700000000000000000023f00c00014fed42c00000000000021310d0000000000000000000000000000000000000000000000000000000000000000_U512,
        ],
        [
            0x40000000fd000000db00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001_U512,
            0x40000000fd000000db0000000000000000000040000000fd000000db000001_U512,
            0xfffffffffffffffffffffffffffffffffffffeffffffffffffffff_U512,
            0x3ffffffffd000000db000040000000fd0000011b000001fd000000db000002_U512,
        ],
        [
            0x40000000fd000000db00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001_U512,
            0x40000000fd000000db0000000000000000000040000000fd000000db0000d3_U512,
            0xfffffffffffffffffffffffffffffffffffffeffffffffffffffff_U512,
            0x3fffff2dfd000000db000040000000fd0000011b0000d3fd000000db0000d4_U512,
        ],
        [
            0x001f000000000000000000000000000000200000000100000000000000000000_U512,
            0x0000000000000000000100000000ffffffffffffffff0000000000002e000000_U512,
            0x1effffffe10000001f_U512,
            0xfffa6e20000591fffffa6e000000_U512,
        ],
        [
            0x7effffff80000000000000000000000000020000440000000000000000000001_U512,
            0x7effffff800000007effffff800000008000ff0000010000_U512,
            0xfffffffffffffffe_U512,
            0x7effffff800000007e0100ff43ff00010001fe0000020001_U512,
        ],
        [
            0x5fd8fffffffffffffffffffffffffffffc090000ce700004d0c9ffffff000001_U512,
            0x2ffffffffffffffffffffffffffffffffff000000030000_U512,
            0x1ff2ffffffffffffff_U512,
            0x2fffffffffffffffc28f300ce102704d0c8ffffff030001_U512,
        ],
        [
            0x62d8fffffffffffffffffffffffffffffc18000000000000000000ca00000001_U512,
            0x2ffffffffffffffffffffffffffffffffff200000000000_U512,
            0x20f2ffffffffffffff_U512,
            0x2fffffffffffffffc34d49fffffffffffff20ca00000001_U512,
        ],
        [
            0x7effffff8000000000000000000000000000000000000000d900000000000001_U512,
            0x7effffff8000000000000000000000000000000000008001_U512,
            0xffffffffffffffff_U512,
            0x7effffff7fffffffffffffffffff7fffd900000000008002_U512,
        ],
        [
            0x0000000000000006400aff20ff00200004e7fd1eff08ffca0afd1eff08ffca0a_U512,
            0x00000000000000210000000000000022_U512,
            0x307c7456554d945ce57749fd52bfdb7f_U512,
            0x1491254b5a0b84a32c_U512,
        ],
        [
            0x7effffff8000000000000000000000000000000000150000d900000000000001_U512,
            0x7effffff8000000000000000000000000000000000f9e101_U512,
            0xffffffffffffffff_U512,
            0x7effffff7fffffffffffffffff1b1effd900000000f9e102_U512,
        ],
        [
            0xffffffff0100000000000000000000000000ffff0000ffffffff0100000000_U512,
            0xffffffff010000000000000000000000ffff0000ffffff_U512,
            0xffffffffffffffff_U512,
            0xffffffff00ffffff0001fffe00010100fffe0100ffffff_U512,
        ],
        [
            0xabfffff0000ffffffffff36363636363636363636d00500000000ffffffffffffe90000ff00000000000000000000ffff0000000000_U512,
            0xabfffff0000ffffffffff36363636363636363636d00500000000ffffffffffffe9ff001f_U512,
            0xffffffffffffffffffffffffffffffffff_U512,
            0xabfffff0000ffffffffff36363636363537371636d00500000001000000fffeffe9ff001f_U512,
        ],
        [
            0xff00ffffffffffffffcaffffffff0100_U512,
            0x0100000000000000ff800000000000ff_U512,
            0xff_U512,
            0xffffffffff017f4afffffffe02ff_U512,
        ],
        [
            0x9000ffffffffffffffcaffffffff0100_U512,
            0x800000000000007fc000000000007f80_U512,
            1_U512,
            0x1000ffffffffff803fcafffffffe8180_U512,
        ],
        [
            // Very special case for reciprocal_3by2().
            170141183460488574554024512018559533058_U512,
            170141183460488574554024512018559533057_U512,
            1_U512,
            1_U512,
        ],
        [
            0x6e2d23924d38f0ab643864e9b2a328a54914f48533114fae3475168bfd74a61ae91e676b4a4f33a5b3b6cc189536ccb4afc46d02b061d6daaf0298c993376ab4_U512,
            170141183460488574554024512018559533057_U512,
            0xdc5a47249a56560d078334729ffb61da211f5d2ec622c22f88bc3b4ebae1abdac6b03621554ef71070bc1e0dc5c301bc_U512,
            0x6dc100ea02272bdcf68a4a5b95f468f8_U512,
        ]
    ]);

    macro_rules! test_cases {
        ($n:ty, $d:ty) => {
            for [numerator, divisor, quotient, remainder] in INTX_TESTS {
                if numerator.bit_len() > <$n>::BITS || divisor.bit_len() > <$d>::BITS {
                    continue;
                }
                let mut numerator = <$n>::from(numerator).into_limbs();
                let mut divisor = <$d>::from(divisor).into_limbs();
                let quotient = <$n>::from(quotient).into_limbs();
                let remainder = <$d>::from(remainder).into_limbs();
                div(&mut numerator, &mut divisor);
                assert_eq!(numerator, quotient);
                assert_eq!(divisor, remainder);
            }
        };
    }

    #[test]
    fn test_div_8x8() {
        use crate::aliases::U512;
        test_cases!(U512, U512);
    }

    #[test]
    fn test_div_6x6() {
        use crate::aliases::U384;
        test_cases!(U384, U384);
    }

    #[test]
    fn test_div_4x4() {
        use crate::aliases::U256;
        test_cases!(U256, U256);
    }

    #[test]
    fn test_div_5x4() {
        use crate::aliases::{U256, U320};
        test_cases!(U320, U256);
    }

    #[test]
    fn test_div_8x4() {
        use crate::aliases::{U256, U512};
        test_cases!(U512, U256);
    }

    #[test]
    #[allow(clippy::unreadable_literal)]
    fn test_div_8by4_one() {
        let mut numerator = [
            0x9c2bcebfa9cca2c6_u64,
            0x274e154bb5e24f7a_u64,
            0xe1442d5d3842be2b_u64,
            0xf18f5adfd420853f_u64,
            0x04ed6127eba3b594_u64,
            0xc5c179973cdb1663_u64,
            0x7d7f67780bb268ff_u64,
            0x0000000000000003_u64,
            0x0000000000000000_u64,
        ];
        let mut divisor = [
            0x0181880b078ab6a1_u64,
            0x62d67f6b7b0bda6b_u64,
            0x92b1840f9c792ded_u64,
            0x0000000000000019_u64,
        ];
        let expected_quotient = [
            0x9128464e61d6b5b3_u64,
            0xd9eea4fc30c5ac6c_u64,
            0x944a2d832d5a6a08_u64,
            0x22f06722e8d883b1_u64,
            0x0000000000000000_u64,
        ];
        let expected_remainder = [
            0x1dfa5a7ea5191b33_u64,
            0xb5aeb3f9ad5e294e_u64,
            0xfc710038c13e4eed_u64,
            0x000000000000000b_u64,
        ];
        div(&mut numerator, &mut divisor);
        assert_eq!(numerator[..5], expected_quotient);
        assert_eq!(divisor, expected_remainder);
    }
}
