use core::arch::x86_64::__m256i;
use core::mem::transmute;

use p3_monty_31::{MontyParametersAVX2, PackedMontyField31AVX2};

use crate::BabyBearParameters;

pub type PackedBabyBearAVX2 = PackedMontyField31AVX2<BabyBearParameters>;

const WIDTH: usize = 8;

impl MontyParametersAVX2 for BabyBearParameters {
    const PACKED_P: __m256i = unsafe { transmute::<[u32; WIDTH], _>([0x78000001; WIDTH]) };
    const PACKED_MU: __m256i = unsafe { transmute::<[u32; WIDTH], _>([0x88000001; WIDTH]) };
}

#[cfg(test)]
mod tests {
    use p3_field_testing::test_packed_field;

    use super::WIDTH;
    use crate::BabyBear;

    const SPECIAL_VALS: [BabyBear; WIDTH] = BabyBear::new_array([
        0x00000000, 0x00000001, 0x78000000, 0x77ffffff, 0x3c000000, 0x0ffffffe, 0x68000003,
        0x70000002,
    ]);

    test_packed_field!(
        crate::PackedBabyBearAVX2,
        &[crate::PackedBabyBearAVX2::ZERO],
        &[crate::PackedBabyBearAVX2::ONE],
        p3_monty_31::PackedMontyField31AVX2::<crate::BabyBearParameters>(super::SPECIAL_VALS)
    );
}
