use core::arch::aarch64::{int32x4_t, uint32x4_t};
use core::mem::transmute;

use p3_monty_31::{MontyParametersNeon, PackedMontyField31Neon};

use crate::BabyBearParameters;

const WIDTH: usize = 4;

impl MontyParametersNeon for BabyBearParameters {
    // SAFETY: This is a valid packed representation of P.
    const PACKED_P: uint32x4_t = unsafe { transmute::<[u32; WIDTH], _>([0x78000001; WIDTH]) };
    // This MU is the same 0x88000001 as elsewhere, just interpreted as an `i32`.
    // SAFETY: This is a valid packed representation of MU.
    const PACKED_MU: int32x4_t = unsafe { transmute::<[i32; WIDTH], _>([-0x77ffffff; WIDTH]) };
}

pub type PackedBabyBearNeon = PackedMontyField31Neon<BabyBearParameters>;

#[cfg(test)]
mod tests {
    use p3_field_testing::test_packed_field;

    use super::WIDTH;
    use crate::BabyBear;

    const SPECIAL_VALS: [BabyBear; WIDTH] =
        BabyBear::new_array([0x00000000, 0x00000001, 0x00000002, 0x78000000]);

    test_packed_field!(
        crate::PackedBabyBearNeon,
        &[crate::PackedBabyBearNeon::ZERO],
        &[crate::PackedBabyBearNeon::ONE],
        p3_monty_31::PackedMontyField31Neon::<crate::BabyBearParameters>(super::SPECIAL_VALS)
    );
}
