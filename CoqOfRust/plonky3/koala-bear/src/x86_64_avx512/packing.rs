use core::arch::x86_64::__m512i;
use core::mem::transmute;

use p3_monty_31::{MontyParametersAVX512, PackedMontyField31AVX512};

use crate::KoalaBearParameters;

pub type PackedKoalaBearAVX512 = PackedMontyField31AVX512<KoalaBearParameters>;

const WIDTH: usize = 16;

impl MontyParametersAVX512 for KoalaBearParameters {
    const PACKED_P: __m512i = unsafe { transmute::<[u32; WIDTH], _>([0x7f000001; WIDTH]) };
    const PACKED_MU: __m512i = unsafe { transmute::<[u32; WIDTH], _>([0x81000001; WIDTH]) };
}

#[cfg(test)]
mod tests {
    use p3_field_testing::test_packed_field;

    use super::WIDTH;
    use crate::KoalaBear;

    const SPECIAL_VALS: [KoalaBear; WIDTH] = KoalaBear::new_array([
        0x00000000, 0x00000001, 0x78000000, 0x77ffffff, 0x3c000000, 0x0ffffffe, 0x68000003,
        0x70000002, 0x00000000, 0x00000001, 0x78000000, 0x77ffffff, 0x3c000000, 0x0ffffffe,
        0x68000003, 0x70000002,
    ]);

    test_packed_field!(
        crate::PackedKoalaBearAVX512,
        &[crate::PackedKoalaBearAVX512::ZERO],
        &[crate::PackedKoalaBearAVX512::ONE],
        p3_monty_31::PackedMontyField31AVX512::<crate::KoalaBearParameters>(super::SPECIAL_VALS)
    );
}
