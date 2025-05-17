use alloc::vec;
use alloc::vec::Vec;

use p3_field::{Field, PackedField, PackedFieldPow2, PackedValue, PrimeCharacteristicRing};
use rand::distr::{Distribution, StandardUniform};
use rand::rngs::SmallRng;
use rand::{Rng, SeedableRng};

fn packed_from_random<PV>(seed: u64) -> PV
where
    PV: PackedValue,
    StandardUniform: Distribution<PV::Value>,
{
    let mut rng = SmallRng::seed_from_u64(seed);
    PV::from_fn(|_| rng.random())
}

/// Interleave arr1 and arr2 using chunks of size i.
fn interleave<T: Copy + Default>(arr1: &[T], arr2: &[T], i: usize) -> (Vec<T>, Vec<T>) {
    let width = arr1.len();
    assert_eq!(width, arr2.len());
    assert_eq!(width % i, 0);

    if i == width {
        return (arr1.to_vec(), arr2.to_vec());
    }

    let mut outleft = vec![T::default(); width];
    let mut outright = vec![T::default(); width];

    let mut flag = false;

    for j in 0..width {
        if j % i == 0 {
            flag = !flag;
        }
        if flag {
            outleft[j] = arr1[j];
            outleft[j + i] = arr2[j];
        } else {
            outright[j - i] = arr1[j];
            outright[j] = arr2[j];
        }
    }

    (outleft, outright)
}

fn test_interleave<PF>(i: usize)
where
    PF: PackedFieldPow2 + Eq,
    StandardUniform: Distribution<PF::Scalar>,
{
    assert!(PF::WIDTH % i == 0);

    let vec1 = packed_from_random::<PF>(0x4ff5dec04791e481);
    let vec2 = packed_from_random::<PF>(0x5806c495e9451f8e);

    let arr1 = vec1.as_slice();
    let arr2 = vec2.as_slice();

    let (res1, res2) = vec1.interleave(vec2, i);
    let (out1, out2) = interleave(arr1, arr2, i);

    assert_eq!(
        res1.as_slice(),
        &out1,
        "Error in left output when testing interleave {}. Data is: \n {:?} \n {:?} \n {:?} \n {:?} \n {:?} \n {:?}.",
        i,
        arr1,
        arr2,
        res1,
        res2,
        out1,
        out2,
    );
    assert_eq!(
        res2.as_slice(),
        &out2,
        "Error in right output when testing interleave {}.",
        i
    );
}

pub fn test_interleaves<PF>()
where
    PF: PackedFieldPow2 + Eq,
    StandardUniform: Distribution<PF::Scalar>,
{
    let mut i = 1;
    while i <= PF::WIDTH {
        test_interleave::<PF>(i);
        i *= 2;
    }
}

pub fn test_packed_linear_combination<PF: PackedField + Eq>()
where
    StandardUniform: Distribution<PF> + Distribution<PF::Scalar>,
{
    let mut rng = SmallRng::seed_from_u64(1);
    let u: [PF::Scalar; 64] = rng.random();
    let v: [PF; 64] = rng.random();

    let mut dot = PF::ZERO;
    assert_eq!(dot, PF::packed_linear_combination::<0>(&u[..0], &v[..0]));
    dot += v[0] * u[0];
    assert_eq!(dot, PF::packed_linear_combination::<1>(&u[..1], &v[..1]));
    dot += v[1] * u[1];
    assert_eq!(dot, PF::packed_linear_combination::<2>(&u[..2], &v[..2]));
    dot += v[2] * u[2];
    assert_eq!(dot, PF::packed_linear_combination::<3>(&u[..3], &v[..3]));
    dot += v[3] * u[3];
    assert_eq!(dot, PF::packed_linear_combination::<4>(&u[..4], &v[..4]));
    dot += v[4] * u[4];
    assert_eq!(dot, PF::packed_linear_combination::<5>(&u[..5], &v[..5]));
    dot += v[5] * u[5];
    assert_eq!(dot, PF::packed_linear_combination::<6>(&u[..6], &v[..6]));
    dot += v[6] * u[6];
    assert_eq!(dot, PF::packed_linear_combination::<7>(&u[..7], &v[..7]));
    dot += v[7] * u[7];
    assert_eq!(dot, PF::packed_linear_combination::<8>(&u[..8], &v[..8]));
    dot += v[8] * u[8];
    assert_eq!(dot, PF::packed_linear_combination::<9>(&u[..9], &v[..9]));
    dot += v[9] * u[9];
    assert_eq!(dot, PF::packed_linear_combination::<10>(&u[..10], &v[..10]));
    dot += v[10] * u[10];
    assert_eq!(dot, PF::packed_linear_combination::<11>(&u[..11], &v[..11]));
    dot += v[11] * u[11];
    assert_eq!(dot, PF::packed_linear_combination::<12>(&u[..12], &v[..12]));
    dot += v[12] * u[12];
    assert_eq!(dot, PF::packed_linear_combination::<13>(&u[..13], &v[..13]));
    dot += v[13] * u[13];
    assert_eq!(dot, PF::packed_linear_combination::<14>(&u[..14], &v[..14]));
    dot += v[14] * u[14];
    assert_eq!(dot, PF::packed_linear_combination::<15>(&u[..15], &v[..15]));
    dot += v[15] * u[15];
    assert_eq!(dot, PF::packed_linear_combination::<16>(&u[..16], &v[..16]));

    let dot_64: PF = u
        .iter()
        .zip(v.iter())
        .fold(PF::ZERO, |acc, (&lhs, &rhs)| acc + (rhs * lhs));
    assert_eq!(dot_64, PF::packed_linear_combination::<64>(&u, &v));
}

pub fn test_vs_scalar<PF>(special_vals: PF)
where
    PF: PackedField + Eq,
    StandardUniform: Distribution<PF::Scalar>,
{
    let vec0: PF = packed_from_random(0x278d9e202925a1d1);
    let vec1: PF = packed_from_random(0xf04cbac0cbad419f);
    let vec_special = special_vals;

    let arr0 = vec0.as_slice();
    let arr1 = vec1.as_slice();

    let vec_sum = vec0 + vec1;
    let arr_sum = vec_sum.as_slice();
    let vec_special_sum_left = vec_special + vec0;
    let arr_special_sum_left = vec_special_sum_left.as_slice();
    let vec_special_sum_right = vec1 + vec_special;
    let arr_special_sum_right = vec_special_sum_right.as_slice();

    let vec_sub = vec0 - vec1;
    let arr_sub = vec_sub.as_slice();
    let vec_special_sub_left = vec_special - vec0;
    let arr_special_sub_left = vec_special_sub_left.as_slice();
    let vec_special_sub_right = vec1 - vec_special;
    let arr_special_sub_right = vec_special_sub_right.as_slice();

    let vec_mul = vec0 * vec1;
    let arr_mul = vec_mul.as_slice();
    let vec_special_mul_left = vec_special * vec0;
    let arr_special_mul_left = vec_special_mul_left.as_slice();
    let vec_special_mul_right = vec1 * vec_special;
    let arr_special_mul_right = vec_special_mul_right.as_slice();

    let vec_neg = -vec0;
    let arr_neg = vec_neg.as_slice();
    let vec_special_neg = -vec_special;
    let arr_special_neg = vec_special_neg.as_slice();

    let vec_exp_3 = vec0.exp_const_u64::<3>();
    let arr_exp_3 = vec_exp_3.as_slice();
    let vec_special_exp_3 = vec_special.exp_const_u64::<3>();
    let arr_special_exp_3 = vec_special_exp_3.as_slice();

    let vec_exp_5 = vec0.exp_const_u64::<5>();
    let arr_exp_5 = vec_exp_5.as_slice();
    let vec_special_exp_5 = vec_special.exp_const_u64::<5>();
    let arr_special_exp_5 = vec_special_exp_5.as_slice();

    let vec_exp_7 = vec0.exp_const_u64::<7>();
    let arr_exp_7 = vec_exp_7.as_slice();
    let vec_special_exp_7 = vec_special.exp_const_u64::<7>();
    let arr_special_exp_7 = vec_special_exp_7.as_slice();

    let special_vals = special_vals.as_slice();
    for i in 0..PF::WIDTH {
        assert_eq!(
            arr_sum[i],
            arr0[i] + arr1[i],
            "Error when testing add consistency of packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_special_sum_left[i],
            special_vals[i] + arr0[i],
            "Error when testing consistency of left add for special values for packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_special_sum_right[i],
            arr1[i] + special_vals[i],
            "Error when testing consistency of right add for special values for packed and scalar at location {}.",
            i
        );

        assert_eq!(
            arr_sub[i],
            arr0[i] - arr1[i],
            "Error when testing sub consistency of packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_special_sub_left[i],
            special_vals[i] - arr0[i],
            "Error when testing consistency of left sub for special values for packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_special_sub_right[i],
            arr1[i] - special_vals[i],
            "Error when testing consistency of right sub for special values for packed and scalar at location {}.",
            i
        );

        assert_eq!(
            arr_mul[i],
            arr0[i] * arr1[i],
            "Error when testing mul consistency of packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_special_mul_left[i],
            special_vals[i] * arr0[i],
            "Error when testing consistency of left mul for special values for packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_special_mul_right[i],
            arr1[i] * special_vals[i],
            "Error when testing consistency of right mul for special values for packed and scalar at location {}.",
            i
        );

        assert_eq!(
            arr_neg[i], -arr0[i],
            "Error when testing neg consistency of packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_special_neg[i], -special_vals[i],
            "Error when testing consistency of neg for special values for packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_exp_3[i],
            arr0[i].exp_const_u64::<3>(),
            "Error when testing exp_const_u64::<3> consistency of packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_special_exp_3[i],
            special_vals[i].exp_const_u64::<3>(),
            "Error when testing consistency of exp_const_u64::<3> for special values for packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_exp_5[i],
            arr0[i].exp_const_u64::<5>(),
            "Error when testing exp_const_u64::<5> consistency of packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_special_exp_5[i],
            special_vals[i].exp_const_u64::<5>(),
            "Error when testing consistency of exp_const_u64::<5> for special values for packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_exp_7[i],
            arr0[i].exp_const_u64::<7>(),
            "Error when testing exp_const_u64::<7> consistency of packed and scalar at location {}.",
            i
        );
        assert_eq!(
            arr_special_exp_7[i],
            special_vals[i].exp_const_u64::<7>(),
            "Error when testing consistency of exp_const_u64::<7> for special values for packed and scalar at location {}.",
            i
        );
    }
}

pub fn test_multiplicative_inverse<PF>()
where
    PF: PackedField + Eq,
    StandardUniform: Distribution<PF::Scalar>,
{
    let vec: PF = packed_from_random(0xb0c7a5153103c5a8);
    let arr = vec.as_slice();
    let vec_inv = PF::from_fn(|i| arr[i].inverse());
    let res = vec * vec_inv;
    assert_eq!(
        res,
        PF::ONE,
        "Error when testing multiplication by inverse."
    );
}

#[macro_export]
macro_rules! test_packed_field {
    ($packedfield:ty, $zeros:expr, $ones:expr, $specials:expr) => {
        mod packed_field_tests {
            use p3_field::PrimeCharacteristicRing;

            #[test]
            fn test_interleaves() {
                $crate::test_interleaves::<$packedfield>();
            }
            #[test]
            fn test_ring_with_eq() {
                $crate::test_ring_with_eq::<$packedfield>($zeros, $ones);
            }
            #[test]
            fn test_packed_linear_combination() {
                $crate::test_packed_linear_combination::<$packedfield>();
            }
            #[test]
            fn test_vs_scalar() {
                $crate::test_vs_scalar::<$packedfield>($specials);
            }
            #[test]
            fn test_multiplicative_inverse() {
                $crate::test_multiplicative_inverse::<$packedfield>();
            }
            #[test]
            fn test_mul_2exp_u64() {
                $crate::test_mul_2exp_u64::<$packedfield>();
            }
        }
    };
}
