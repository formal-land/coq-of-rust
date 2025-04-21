use core::arch::aarch64::{int32x4_t, uint32x4_t};
use core::mem::transmute;

use p3_monty_31::{MontyParametersNeon, PackedMontyField31Neon};

use crate::KoalaBearParameters;

const WIDTH: usize = 4;

impl MontyParametersNeon for KoalaBearParameters {
    const PACKED_P: uint32x4_t = unsafe { transmute::<[u32; WIDTH], _>([0x7f000001; WIDTH]) };
    // This MU is the same 0x88000001 as elsewhere, just interpreted as an `i32`.
    const PACKED_MU: int32x4_t = unsafe { transmute::<[i32; WIDTH], _>([-0x7effffff; WIDTH]) };
}

pub type PackedKoalaBearNeon = PackedMontyField31Neon<KoalaBearParameters>;

#[cfg(test)]
mod tests {
    use p3_field_testing::test_packed_field;

    use super::WIDTH;
    use crate::KoalaBear;

    const SPECIAL_VALS: [KoalaBear; WIDTH] =
        KoalaBear::new_array([0x00000000, 0x00000001, 0x00000002, 0x7f000000]);

    test_packed_field!(
        crate::PackedKoalaBearNeon,
        &[crate::PackedKoalaBearNeon::ZERO],
        &[crate::PackedKoalaBearNeon::ONE],
        p3_monty_31::PackedMontyField31Neon::<crate::KoalaBearParameters>(super::SPECIAL_VALS)
    );
}
