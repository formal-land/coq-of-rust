//! MDS matrices over the Mersenne31 field, and permutations defined by them.
//!
//! NB: Not all sizes have fast implementations of their permutations.
//! Supported sizes: 8, 12, 16, 32, 64.
//! Sizes 8 and 12 are from Plonky2, size 16 was found as part of concurrent
//! work by Angus Gruen and Hamish Ivey-Law. Other sizes are from Ulrich Haböck's
//! database.

use p3_field::PrimeCharacteristicRing;
use p3_field::integers::QuotientMap;
use p3_mds::MdsPermutation;
use p3_mds::karatsuba_convolution::Convolve;
use p3_mds::util::{dot_product, first_row_to_first_col};
use p3_symmetric::Permutation;

use crate::Mersenne31;

#[derive(Clone, Debug, Default)]
pub struct MdsMatrixMersenne31;

/// Instantiate convolution for "small" RHS vectors over Mersenne31.
///
/// Here "small" means N = len(rhs) <= 16 and sum(r for r in rhs) <
/// 2^24 (roughly), though in practice the sum will be less than 2^9.
struct SmallConvolveMersenne31;
impl Convolve<Mersenne31, i64, i64, i64> for SmallConvolveMersenne31 {
    /// Return the lift of an (almost) reduced Mersenne31 element.
    /// The Mersenne31 implementation guarantees that
    /// 0 <= input.value <= P < 2^31.
    #[inline(always)]
    fn read(input: Mersenne31) -> i64 {
        input.value as i64
    }

    /// FIXME: Refactor the dot product
    /// For a convolution of size N, |x| < N * 2^31 and (as per the
    /// assumption above), |y| < 2^24. So the product is at most N * 2^55
    /// which will not overflow for N <= 16.
    #[inline(always)]
    fn parity_dot<const N: usize>(u: [i64; N], v: [i64; N]) -> i64 {
        dot_product(u, v)
    }

    /// The assumptions above mean z < N^2 * 2^55, which is at most
    /// 2^63 when N <= 16.
    ///
    /// NB: Even though intermediate values could be negative, the
    /// output must be non-negative since the inputs were
    /// non-negative.
    #[inline(always)]
    fn reduce(z: i64) -> Mersenne31 {
        debug_assert!(z >= 0);
        Mersenne31::from_u64(z as u64)
    }
}

/// Instantiate convolution for "large" RHS vectors over Mersenne31.
///
/// Here "large" means the elements can be as big as the field
/// characteristic, and the size N of the RHS is <= 64.
struct LargeConvolveMersenne31;
impl Convolve<Mersenne31, i64, i64, i64> for LargeConvolveMersenne31 {
    /// Return the lift of an (almost) reduced Mersenne31 element.
    /// The Mersenne31 implementation guarantees that
    /// 0 <= input.value <= P < 2^31.
    #[inline(always)]
    fn read(input: Mersenne31) -> i64 {
        input.value as i64
    }

    #[inline]
    fn parity_dot<const N: usize>(u: [i64; N], v: [i64; N]) -> i64 {
        // For a convolution of size N, |x|, |y| < N * 2^31, so the product
        // could be as much as N^2 * 2^62. This will overflow an i64, so
        // we first widen to i128.

        let mut dp = 0i128;
        for i in 0..N {
            dp += u[i] as i128 * v[i] as i128;
        }

        const LOWMASK: i128 = (1 << 42) - 1; // Gets the bits lower than 42.
        const HIGHMASK: i128 = !LOWMASK; // Gets all bits higher than 42.

        let low_bits = (dp & LOWMASK) as i64; // low_bits < 2**42
        let high_bits = ((dp & HIGHMASK) >> 31) as i64; // |high_bits| < 2**(n - 31)

        // Proof that low_bits + high_bits is congruent to dp (mod p)
        // and congruent to dp (mod 2^11):
        //
        // The individual bounds clearly show that low_bits +
        // high_bits < 2**(n - 30).
        //
        // Next observe that low_bits + high_bits = input - (2**31 -
        // 1) * (high_bits) = input mod P.
        //
        // Finally note that 2**11 divides high_bits and so low_bits +
        // high_bits = low_bits mod 2**11 = input mod 2**11.

        low_bits + high_bits
    }

    #[inline]
    fn reduce(z: i64) -> Mersenne31 {
        // After the dot product, the maximal size is N^2 * 2^62 < 2^74
        // as N = 64 is the biggest size. So, after the partial
        // reduction, the output z of parity dot satisfies |z| < 2^44
        // (Where 44 is 74 - 30).
        //
        // In the recombining steps, conv maps (wo, w1) -> ((wo + w1)/2,
        // (wo + w1)/2) which has no effect on the maximal size. (Indeed,
        // it makes sizes almost strictly smaller).
        //
        // On the other hand, negacyclic_conv (ignoring the re-index)
        // recombines as: (w0, w1, w2) -> (w0 + w1, w2 - w0 - w1). Hence
        // if the input is <= K, the output is <= 3K.
        //
        // Thus the values appearing at the end are bounded by 3^n 2^44
        // where n is the maximal number of negacyclic_conv recombination
        // steps. When N = 64, we need to recombine for singed_conv_32,
        // singed_conv_16, singed_conv_8 so the overall bound will be 3^3
        // 2^44 < 32 * 2^44 < 2^49.
        debug_assert!(z > -(1i64 << 49));
        debug_assert!(z < (1i64 << 49));

        const MASK: i64 = (1 << 31) - 1;
        // Morally, our value is a i62 not a i64 as the top 3 bits are
        // guaranteed to be equal.
        let low_bits = unsafe {
            // This is safe as 0 <= z & MASK < 2^31
            Mersenne31::from_canonical_unchecked((z & MASK) as u32)
        };

        let high_bits = ((z >> 31) & MASK) as i32;
        let sign_bits = (z >> 62) as i32;

        let high = unsafe {
            // This is safe as high_bits + sign_bits > 0 as by assumption b[63] = b[61].
            Mersenne31::from_canonical_unchecked((high_bits + sign_bits) as u32)
        };
        low_bits + high
    }
}

const MATRIX_CIRC_MDS_8_SML_ROW: [i64; 8] = [7, 1, 3, 8, 8, 3, 4, 9];

impl Permutation<[Mersenne31; 8]> for MdsMatrixMersenne31 {
    fn permute(&self, input: [Mersenne31; 8]) -> [Mersenne31; 8] {
        const MATRIX_CIRC_MDS_8_SML_COL: [i64; 8] =
            first_row_to_first_col(&MATRIX_CIRC_MDS_8_SML_ROW);
        SmallConvolveMersenne31::apply(
            input,
            MATRIX_CIRC_MDS_8_SML_COL,
            SmallConvolveMersenne31::conv8,
        )
    }

    fn permute_mut(&self, input: &mut [Mersenne31; 8]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Mersenne31, 8> for MdsMatrixMersenne31 {}

const MATRIX_CIRC_MDS_12_SML_ROW: [i64; 12] = [1, 1, 2, 1, 8, 9, 10, 7, 5, 9, 4, 10];

impl Permutation<[Mersenne31; 12]> for MdsMatrixMersenne31 {
    fn permute(&self, input: [Mersenne31; 12]) -> [Mersenne31; 12] {
        const MATRIX_CIRC_MDS_12_SML_COL: [i64; 12] =
            first_row_to_first_col(&MATRIX_CIRC_MDS_12_SML_ROW);
        SmallConvolveMersenne31::apply(
            input,
            MATRIX_CIRC_MDS_12_SML_COL,
            SmallConvolveMersenne31::conv12,
        )
    }

    fn permute_mut(&self, input: &mut [Mersenne31; 12]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Mersenne31, 12> for MdsMatrixMersenne31 {}

const MATRIX_CIRC_MDS_16_SML_ROW: [i64; 16] =
    [1, 1, 51, 1, 11, 17, 2, 1, 101, 63, 15, 2, 67, 22, 13, 3];

impl Permutation<[Mersenne31; 16]> for MdsMatrixMersenne31 {
    fn permute(&self, input: [Mersenne31; 16]) -> [Mersenne31; 16] {
        const MATRIX_CIRC_MDS_16_SML_COL: [i64; 16] =
            first_row_to_first_col(&MATRIX_CIRC_MDS_16_SML_ROW);
        SmallConvolveMersenne31::apply(
            input,
            MATRIX_CIRC_MDS_16_SML_COL,
            SmallConvolveMersenne31::conv16,
        )
    }

    fn permute_mut(&self, input: &mut [Mersenne31; 16]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Mersenne31, 16> for MdsMatrixMersenne31 {}

#[rustfmt::skip]
const MATRIX_CIRC_MDS_32_MERSENNE31_ROW: [i64; 32] = [
    0x1896DC78, 0x559D1E29, 0x04EBD732, 0x3FF449D7,
    0x2DB0E2CE, 0x26776B85, 0x76018E57, 0x1025FA13,
    0x06486BAB, 0x37706EBA, 0x25EB966B, 0x113C24E5,
    0x2AE20EC4, 0x5A27507C, 0x0CD38CF1, 0x761C10E5,
    0x19E3EF1A, 0x032C730F, 0x35D8AF83, 0x651DF13B,
    0x7EC3DB1A, 0x6A146994, 0x588F9145, 0x09B79455,
    0x7FDA05EC, 0x19FE71A8, 0x6988947A, 0x624F1D31,
    0x500BB628, 0x0B1428CE, 0x3A62E1D6, 0x77692387
];

impl Permutation<[Mersenne31; 32]> for MdsMatrixMersenne31 {
    fn permute(&self, input: [Mersenne31; 32]) -> [Mersenne31; 32] {
        const MATRIX_CIRC_MDS_32_MERSENNE31_COL: [i64; 32] =
            first_row_to_first_col(&MATRIX_CIRC_MDS_32_MERSENNE31_ROW);
        LargeConvolveMersenne31::apply(
            input,
            MATRIX_CIRC_MDS_32_MERSENNE31_COL,
            LargeConvolveMersenne31::conv32,
        )
    }

    fn permute_mut(&self, input: &mut [Mersenne31; 32]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Mersenne31, 32> for MdsMatrixMersenne31 {}

#[rustfmt::skip]
const MATRIX_CIRC_MDS_64_MERSENNE31_ROW: [i64; 64] = [
    0x570227A5, 0x3702983F, 0x4B7B3B0A, 0x74F13DE3,
    0x485314B0, 0x0157E2EC, 0x1AD2E5DE, 0x721515E3,
    0x5452ADA3, 0x0C74B6C1, 0x67DA9450, 0x33A48369,
    0x3BDBEE06, 0x7C678D5E, 0x160F16D3, 0x54888B8C,
    0x666C7AA6, 0x113B89E2, 0x2A403CE2, 0x18F9DF42,
    0x2A685E84, 0x49EEFDE5, 0x5D044806, 0x560A41F8,
    0x69EF1BD0, 0x2CD15786, 0x62E07766, 0x22A231E2,
    0x3CFCF40C, 0x4E8F63D8, 0x69657A15, 0x466B4B2D,
    0x4194B4D2, 0x1E9A85EA, 0x39709C27, 0x4B030BF3,
    0x655DCE1D, 0x251F8899, 0x5B2EA879, 0x1E10E42F,
    0x31F5BE07, 0x2AFBB7F9, 0x3E11021A, 0x5D97A17B,
    0x6F0620BD, 0x5DBFC31D, 0x76C4761D, 0x21938559,
    0x33777473, 0x71F0E92C, 0x0B9872A1, 0x4C2411F9,
    0x545B7C96, 0x20256BAF, 0x7B8B493E, 0x33AD525C,
    0x15EAEA1C, 0x6D2D1A21, 0x06A81D14, 0x3FACEB4F,
    0x130EC21C, 0x3C84C4F5, 0x50FD67C0, 0x30FDD85A,
];

impl Permutation<[Mersenne31; 64]> for MdsMatrixMersenne31 {
    fn permute(&self, input: [Mersenne31; 64]) -> [Mersenne31; 64] {
        const MATRIX_CIRC_MDS_64_MERSENNE31_COL: [i64; 64] =
            first_row_to_first_col(&MATRIX_CIRC_MDS_64_MERSENNE31_ROW);
        LargeConvolveMersenne31::apply(
            input,
            MATRIX_CIRC_MDS_64_MERSENNE31_COL,
            LargeConvolveMersenne31::conv64,
        )
    }

    fn permute_mut(&self, input: &mut [Mersenne31; 64]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Mersenne31, 64> for MdsMatrixMersenne31 {}

#[cfg(test)]
mod tests {
    use p3_symmetric::Permutation;

    use super::{MdsMatrixMersenne31, Mersenne31};

    #[test]
    fn mersenne8() {
        let input: [Mersenne31; 8] = Mersenne31::new_array([
            1741044457, 327154658, 318297696, 1528828225, 468360260, 1271368222, 1906288587,
            1521884224,
        ]);

        let output = MdsMatrixMersenne31.permute(input);

        let expected: [Mersenne31; 8] = Mersenne31::new_array([
            895992680, 1343855369, 2107796831, 266468728, 846686506, 252887121, 205223309,
            260248790,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn mersenne12() {
        let input: [Mersenne31; 12] = Mersenne31::new_array([
            1232740094, 661555540, 11024822, 1620264994, 471137070, 276755041, 1316882747,
            1023679816, 1675266989, 743211887, 44774582, 1990989306,
        ]);

        let output = MdsMatrixMersenne31.permute(input);

        let expected: [Mersenne31; 12] = Mersenne31::new_array([
            860812289, 399778981, 1228500858, 798196553, 673507779, 1116345060, 829764188,
            138346433, 578243475, 553581995, 578183208, 1527769050,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn mersenne16() {
        let input: [Mersenne31; 16] = Mersenne31::new_array([
            1431168444, 963811518, 88067321, 381314132, 908628282, 1260098295, 980207659,
            150070493, 357706876, 2014609375, 387876458, 1621671571, 183146044, 107201572,
            166536524, 2078440788,
        ]);

        let output = MdsMatrixMersenne31.permute(input);

        let expected: [Mersenne31; 16] = Mersenne31::new_array([
            1858869691, 1607793806, 1200396641, 1400502985, 1511630695, 187938132, 1332411488,
            2041577083, 2014246632, 802022141, 796807132, 1647212930, 813167618, 1867105010,
            508596277, 1457551581,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn mersenne32() {
        let input: [Mersenne31; 32] = Mersenne31::new_array([
            873912014, 1112497426, 300405095, 4255553, 1234979949, 156402357, 1952135954,
            718195399, 1041748465, 683604342, 184275751, 1184118518, 214257054, 1293941921,
            64085758, 710448062, 1133100009, 350114887, 1091675272, 671421879, 1226105999,
            546430131, 1298443967, 1787169653, 2129310791, 1560307302, 471771931, 1191484402,
            1550203198, 1541319048, 229197040, 839673789,
        ]);

        let output = MdsMatrixMersenne31.permute(input);

        let expected: [Mersenne31; 32] = Mersenne31::new_array([
            1439049928, 890642852, 694402307, 713403244, 553213342, 1049445650, 321709533,
            1195683415, 2118492257, 623077773, 96734062, 990488164, 1674607608, 749155000,
            353377854, 966432998, 1114654884, 1370359248, 1624965859, 685087760, 1631836645,
            1615931812, 2061986317, 1773551151, 1449911206, 1951762557, 545742785, 582866449,
            1379774336, 229242759, 1871227547, 752848413,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn mersenne64() {
        let input: [Mersenne31; 64] = Mersenne31::new_array([
            837269696, 1509031194, 413915480, 1889329185, 315502822, 1529162228, 1454661012,
            1015826742, 973381409, 1414676304, 1449029961, 1968715566, 2027226497, 1721820509,
            434042616, 1436005045, 1680352863, 651591867, 260585272, 1078022153, 703990572,
            269504423, 1776357592, 1174979337, 1142666094, 1897872960, 1387995838, 250774418,
            776134750, 73930096, 194742451, 1860060380, 666407744, 669566398, 963802147,
            2063418105, 1772573581, 998923482, 701912753, 1716548204, 860820931, 1680395948,
            949886256, 1811558161, 501734557, 1671977429, 463135040, 1911493108, 207754409,
            608714758, 1553060084, 1558941605, 980281686, 2014426559, 650527801, 53015148,
            1521176057, 720530872, 713593252, 88228433, 1194162313, 1922416934, 1075145779,
            344403794,
        ]);

        let output = MdsMatrixMersenne31.permute(input);

        let expected: [Mersenne31; 64] = Mersenne31::new_array([
            1599981950, 252630853, 1171557270, 116468420, 1269245345, 666203050, 46155642,
            1701131520, 530845775, 508460407, 630407239, 1731628135, 1199144768, 295132047,
            77536342, 1472377703, 30752443, 1300339617, 18647556, 1267774380, 1194573079,
            1624665024, 646848056, 1667216490, 1184843555, 1250329476, 254171597, 1902035936,
            1706882202, 964921003, 952266538, 1215696284, 539510504, 1056507562, 1393151480,
            733644883, 1663330816, 1100715048, 991108703, 1671345065, 1376431774, 408310416,
            313176996, 743567676, 304660642, 1842695838, 958201635, 1650792218, 541570244,
            968523062, 1958918704, 1866282698, 849808680, 1193306222, 794153281, 822835360,
            135282913, 1149868448, 2068162123, 1474283743, 2039088058, 720305835, 746036736,
            671006610,
        ]);

        assert_eq!(output, expected);
    }
}
