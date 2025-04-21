use crate::PrimeCharacteristicRing;

pub(crate) const fn bits_u64(n: u64) -> usize {
    (64 - n.leading_zeros()) as usize
}

/// Compute the exponential `x -> x^1717986917` using a custom addition chain.
///
/// This map computes the fifth root of `x` if `x` is a member of the field `Mersenne31`.
/// This follows from the computation: `5 * 1717986917 = 4*(2^31 - 2) + 1 = 1 mod p - 1`.
pub fn exp_1717986917<R: PrimeCharacteristicRing>(val: R) -> R {
    // Note the binary expansion: 1717986917 = 1100110011001100110011001100101_2
    // This uses 30 Squares + 7 Multiplications => 37 Operations total.
    // Suspect it's possible to improve this with enough effort. For example 1717986918 takes only 4 Multiplications.
    let p1 = val;
    let p10 = p1.square();
    let p11 = p10.clone() * p1;
    let p101 = p10 * p11.clone();
    let p110000 = p11.exp_power_of_2(4);
    let p110011 = p110000 * p11.clone();
    let p11001100000000 = p110011.exp_power_of_2(8);
    let p11001100110011 = p11001100000000.clone() * p110011;
    let p1100110000000000000000 = p11001100000000.exp_power_of_2(8);
    let p1100110011001100110011 = p1100110000000000000000 * p11001100110011;
    let p11001100110011001100110000 = p1100110011001100110011.exp_power_of_2(4);
    let p11001100110011001100110011 = p11001100110011001100110000 * p11;
    let p1100110011001100110011001100000 = p11001100110011001100110011.exp_power_of_2(5);
    p1100110011001100110011001100000 * p101
}

/// Compute the exponential `x -> x^1420470955` using a custom addition chain.
///
/// This map computes the third root of `x` if `x` is a member of the field `KoalaBear`.
/// This follows from the computation: `3 * 1420470955 = 2*(2^31 - 2^24) + 1 = 1 mod (p - 1)`.
pub fn exp_1420470955<R: PrimeCharacteristicRing>(val: R) -> R {
    // Note the binary expansion: 1420470955 = 1010100101010101010101010101011_2
    // This uses 29 Squares + 7 Multiplications => 36 Operations total.
    // Suspect it's possible to improve this with enough effort.
    let p1 = val;
    let p100 = p1.exp_power_of_2(2);
    let p101 = p100.clone() * p1.clone();
    let p10000 = p100.exp_power_of_2(2);
    let p10101 = p10000 * p101;
    let p10101000000 = p10101.exp_power_of_2(6);
    let p10101010101 = p10101000000.clone() * p10101.clone();
    let p101010010101 = p10101000000 * p10101010101.clone();
    let p101010010101000000000000 = p101010010101.exp_power_of_2(12);
    let p101010010101010101010101 = p101010010101000000000000 * p10101010101;
    let p101010010101010101010101000000 = p101010010101010101010101.exp_power_of_2(6);
    let p101010010101010101010101010101 = p101010010101010101010101000000 * p10101;
    let p1010100101010101010101010101010 = p101010010101010101010101010101.square();
    p1010100101010101010101010101010 * p1
}

/// Compute the exponential `x -> x^1725656503` using a custom addition chain.
///
/// This map computes the seventh root of `x` if `x` is a member of the field `BabyBear`.
/// This follows from the computation: `7 * 1725656503 = 6*(2^31 - 2^27) + 1 = 1 mod (p - 1)`.
pub fn exp_1725656503<R: PrimeCharacteristicRing>(val: R) -> R {
    // Note the binary expansion: 1725656503 = 1100110110110110110110110110111_2
    // This uses 29 Squares + 8 Multiplications => 37 Operations total.
    // Suspect it's possible to improve this with enough effort.
    let p1 = val;
    let p10 = p1.square();
    let p11 = p10 * p1.clone();
    let p110 = p11.square();
    let p111 = p110.clone() * p1;
    let p11000 = p110.exp_power_of_2(2);
    let p11011 = p11000.clone() * p11;
    let p11000000 = p11000.exp_power_of_2(3);
    let p11011011 = p11000000.clone() * p11011;
    let p110011011 = p11011011.clone() * p11000000;
    let p110011011000000000 = p110011011.exp_power_of_2(9);
    let p110011011011011011 = p110011011000000000 * p11011011.clone();
    let p110011011011011011000000000 = p110011011011011011.exp_power_of_2(9);
    let p110011011011011011011011011 = p110011011011011011000000000 * p11011011;
    let p1100110110110110110110110110000 = p110011011011011011011011011.exp_power_of_2(4);
    p1100110110110110110110110110000 * p111
}

/// Compute the exponential `x -> x^10540996611094048183` using a custom addition chain.
///
/// This map computes the seventh root of `x` if `x` is a member of the field `Goldilocks`.
/// This follows from the computation: `7 * 10540996611094048183 = 4*(2^64 - 2**32) + 1 = 1 mod (p - 1)`.
pub fn exp_10540996611094048183<R: PrimeCharacteristicRing>(val: R) -> R {
    // Note the binary expansion: 10540996611094048183 = 1001001001001001001001001001000110110110110110110110110110110111_2.
    // This uses 63 Squares + 8 Multiplications => 71 Operations total.
    // Suspect it's possible to improve this a little with enough effort.
    let p1 = val;
    let p10 = p1.square();
    let p11 = p10.clone() * p1;
    let p100 = p10.square();
    let p111 = p100.clone() * p11.clone();
    let p100000000000000000000000000000000 = p100.exp_power_of_2(30);
    let p100000000000000000000000000000011 = p100000000000000000000000000000000 * p11;
    let p100000000000000000000000000000011000 =
        p100000000000000000000000000000011.exp_power_of_2(3);
    let p100100000000000000000000000000011011 =
        p100000000000000000000000000000011000 * p100000000000000000000000000000011;
    let p100100000000000000000000000000011011000000 =
        p100100000000000000000000000000011011.exp_power_of_2(6);
    let p100100100100000000000000000000011011011011 =
        p100100000000000000000000000000011011000000 * p100100000000000000000000000000011011.clone();
    let p100100100100000000000000000000011011011011000000000000 =
        p100100100100000000000000000000011011011011.exp_power_of_2(12);
    let p100100100100100100100100000000011011011011011011011011 =
        p100100100100000000000000000000011011011011000000000000
            * p100100100100000000000000000000011011011011;
    let p100100100100100100100100000000011011011011011011011011000000 =
        p100100100100100100100100000000011011011011011011011011.exp_power_of_2(6);
    let p100100100100100100100100100100011011011011011011011011011011 =
        p100100100100100100100100000000011011011011011011011011000000
            * p100100000000000000000000000000011011;
    let p1001001001001001001001001001000110110110110110110110110110110000 =
        p100100100100100100100100100100011011011011011011011011011011.exp_power_of_2(4);

    p1001001001001001001001001001000110110110110110110110110110110000 * p111
}
