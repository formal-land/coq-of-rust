use core::arch::x86_64::{
    __m128i, _mm_add_epi64, _mm_andnot_si128, _mm_or_si128, _mm_slli_epi64, _mm_srli_epi64,
    _mm_xor_si128,
};
use core::mem::transmute;

use p3_symmetric::{CryptographicPermutation, Permutation};

use crate::KeccakF;

pub const VECTOR_LEN: usize = 2;

const RC: [__m128i; 24] = unsafe {
    transmute([
        [1u64; 2],
        [0x8082u64; 2],
        [0x800000000000808au64; 2],
        [0x8000000080008000u64; 2],
        [0x808bu64; 2],
        [0x80000001u64; 2],
        [0x8000000080008081u64; 2],
        [0x8000000000008009u64; 2],
        [0x8au64; 2],
        [0x88u64; 2],
        [0x80008009u64; 2],
        [0x8000000au64; 2],
        [0x8000808bu64; 2],
        [0x800000000000008bu64; 2],
        [0x8000000000008089u64; 2],
        [0x8000000000008003u64; 2],
        [0x8000000000008002u64; 2],
        [0x8000000000000080u64; 2],
        [0x800au64; 2],
        [0x800000008000000au64; 2],
        [0x8000000080008081u64; 2],
        [0x8000000000008080u64; 2],
        [0x80000001u64; 2],
        [0x8000000080008008u64; 2],
    ])
};

#[inline(always)]
fn form_matrix(buf: [__m128i; 25]) -> [[__m128i; 5]; 5] {
    unsafe { transmute(buf) }
}

#[inline(always)]
fn flatten(mat: [[__m128i; 5]; 5]) -> [__m128i; 25] {
    unsafe { transmute(mat) }
}

#[inline(always)]
fn rol_1(a: __m128i) -> __m128i {
    unsafe {
        let shl = _mm_add_epi64(a, a);
        let shr = _mm_srli_epi64::<63>(a);
        _mm_or_si128(shl, shr)
    }
}

#[cfg(target_feature = "ssse3")]
#[inline(always)]
fn rol_8(a: __m128i) -> __m128i {
    use core::arch::x86_64::_mm_shuffle_epi8;
    const ROL_8_CTRL: __m128i = unsafe {
        transmute::<[u8; 16], _>([
            0o07, 0o00, 0o01, 0o02, 0o03, 0o04, 0o05, 0o06, 0o17, 0o10, 0o11, 0o12, 0o13, 0o14,
            0o15, 0o16,
        ])
    };
    unsafe { _mm_shuffle_epi8(a, ROL_8_CTRL) }
}

#[cfg(not(target_feature = "ssse3"))]
#[inline(always)]
fn rol_8(a: __m128i) -> __m128i {
    rol::<8, { 64 - 8 }>(a)
}

#[cfg(target_feature = "ssse3")]
#[inline(always)]
fn rol_56(a: __m128i) -> __m128i {
    use core::arch::x86_64::_mm_shuffle_epi8;
    const ROL_56_CTRL: __m128i = unsafe {
        transmute::<[u8; 16], _>([
            0o01, 0o02, 0o03, 0o04, 0o05, 0o06, 0o07, 0o00, 0o11, 0o12, 0o13, 0o14, 0o15, 0o16,
            0o17, 0o10,
        ])
    };
    unsafe { _mm_shuffle_epi8(a, ROL_56_CTRL) }
}

#[cfg(not(target_feature = "ssse3"))]
#[inline(always)]
fn rol_56(a: __m128i) -> __m128i {
    rol::<56, { 64 - 56 }>(a)
}

#[inline(always)]
fn rol<const SHL_AMT: i32, const SHR_AMT: i32>(a: __m128i) -> __m128i {
    unsafe {
        let shl = _mm_slli_epi64::<SHL_AMT>(a);
        let shr = _mm_srli_epi64::<SHR_AMT>(a);
        _mm_or_si128(shl, shr)
    }
}

#[inline(always)]
fn get_theta_parities(state: [[__m128i; 5]; 5]) -> [__m128i; 5] {
    unsafe {
        let mut par0 = _mm_xor_si128(state[0][0], state[1][0]);
        let mut par1 = _mm_xor_si128(state[0][1], state[1][1]);
        let mut par2 = _mm_xor_si128(state[0][2], state[1][2]);
        let mut par3 = _mm_xor_si128(state[0][3], state[1][3]);
        let mut par4 = _mm_xor_si128(state[0][4], state[1][4]);

        par0 = _mm_xor_si128(par0, state[2][0]);
        par1 = _mm_xor_si128(par1, state[2][1]);
        par2 = _mm_xor_si128(par2, state[2][2]);
        par3 = _mm_xor_si128(par3, state[2][3]);
        par4 = _mm_xor_si128(par4, state[2][4]);

        par0 = _mm_xor_si128(par0, state[3][0]);
        par1 = _mm_xor_si128(par1, state[3][1]);
        par2 = _mm_xor_si128(par2, state[3][2]);
        par3 = _mm_xor_si128(par3, state[3][3]);
        par4 = _mm_xor_si128(par4, state[3][4]);

        par0 = _mm_xor_si128(par0, state[4][0]);
        par1 = _mm_xor_si128(par1, state[4][1]);
        par2 = _mm_xor_si128(par2, state[4][2]);
        par3 = _mm_xor_si128(par3, state[4][3]);
        par4 = _mm_xor_si128(par4, state[4][4]);

        [
            _mm_xor_si128(par4, rol_1(par1)),
            _mm_xor_si128(par0, rol_1(par2)),
            _mm_xor_si128(par1, rol_1(par3)),
            _mm_xor_si128(par2, rol_1(par4)),
            _mm_xor_si128(par3, rol_1(par0)),
        ]
    }
}

#[inline(always)]
fn theta(state: [[__m128i; 5]; 5]) -> [[__m128i; 5]; 5] {
    let theta_parities = get_theta_parities(state);

    unsafe {
        [
            [
                _mm_xor_si128(state[0][0], theta_parities[0]),
                _mm_xor_si128(state[0][1], theta_parities[1]),
                _mm_xor_si128(state[0][2], theta_parities[2]),
                _mm_xor_si128(state[0][3], theta_parities[3]),
                _mm_xor_si128(state[0][4], theta_parities[4]),
            ],
            [
                _mm_xor_si128(state[1][0], theta_parities[0]),
                _mm_xor_si128(state[1][1], theta_parities[1]),
                _mm_xor_si128(state[1][2], theta_parities[2]),
                _mm_xor_si128(state[1][3], theta_parities[3]),
                _mm_xor_si128(state[1][4], theta_parities[4]),
            ],
            [
                _mm_xor_si128(state[2][0], theta_parities[0]),
                _mm_xor_si128(state[2][1], theta_parities[1]),
                _mm_xor_si128(state[2][2], theta_parities[2]),
                _mm_xor_si128(state[2][3], theta_parities[3]),
                _mm_xor_si128(state[2][4], theta_parities[4]),
            ],
            [
                _mm_xor_si128(state[3][0], theta_parities[0]),
                _mm_xor_si128(state[3][1], theta_parities[1]),
                _mm_xor_si128(state[3][2], theta_parities[2]),
                _mm_xor_si128(state[3][3], theta_parities[3]),
                _mm_xor_si128(state[3][4], theta_parities[4]),
            ],
            [
                _mm_xor_si128(state[4][0], theta_parities[0]),
                _mm_xor_si128(state[4][1], theta_parities[1]),
                _mm_xor_si128(state[4][2], theta_parities[2]),
                _mm_xor_si128(state[4][3], theta_parities[3]),
                _mm_xor_si128(state[4][4], theta_parities[4]),
            ],
        ]
    }
}

#[inline(always)]
fn rho(state: [[__m128i; 5]; 5]) -> [[__m128i; 5]; 5] {
    [
        [
            state[0][0],
            rol_1(state[0][1]),
            rol::<62, { 64 - 62 }>(state[0][2]),
            rol::<28, { 64 - 28 }>(state[0][3]),
            rol::<27, { 64 - 27 }>(state[0][4]),
        ],
        [
            rol::<36, { 64 - 36 }>(state[1][0]),
            rol::<44, { 64 - 44 }>(state[1][1]),
            rol::<6, { 64 - 6 }>(state[1][2]),
            rol::<55, { 64 - 55 }>(state[1][3]),
            rol::<20, { 64 - 20 }>(state[1][4]),
        ],
        [
            rol::<3, { 64 - 3 }>(state[2][0]),
            rol::<10, { 64 - 10 }>(state[2][1]),
            rol::<43, { 64 - 43 }>(state[2][2]),
            rol::<25, { 64 - 25 }>(state[2][3]),
            rol::<39, { 64 - 39 }>(state[2][4]),
        ],
        [
            rol::<41, { 64 - 41 }>(state[3][0]),
            rol::<45, { 64 - 45 }>(state[3][1]),
            rol::<15, { 64 - 15 }>(state[3][2]),
            rol::<21, { 64 - 21 }>(state[3][3]),
            rol_8(state[3][4]),
        ],
        [
            rol::<18, { 64 - 18 }>(state[4][0]),
            rol::<2, { 64 - 2 }>(state[4][1]),
            rol::<61, { 64 - 61 }>(state[4][2]),
            rol_56(state[4][3]),
            rol::<14, { 64 - 14 }>(state[4][4]),
        ],
    ]
}

#[inline(always)]
fn pi(state: [[__m128i; 5]; 5]) -> [[__m128i; 5]; 5] {
    [
        [
            state[0][0],
            state[1][1],
            state[2][2],
            state[3][3],
            state[4][4],
        ],
        [
            state[0][3],
            state[1][4],
            state[2][0],
            state[3][1],
            state[4][2],
        ],
        [
            state[0][1],
            state[1][2],
            state[2][3],
            state[3][4],
            state[4][0],
        ],
        [
            state[0][4],
            state[1][0],
            state[2][1],
            state[3][2],
            state[4][3],
        ],
        [
            state[0][2],
            state[1][3],
            state[2][4],
            state[3][0],
            state[4][1],
        ],
    ]
}

#[inline(always)]
fn chi_row(row: [__m128i; 5]) -> [__m128i; 5] {
    unsafe {
        [
            _mm_xor_si128(row[0], _mm_andnot_si128(row[1], row[2])),
            _mm_xor_si128(row[1], _mm_andnot_si128(row[2], row[3])),
            _mm_xor_si128(row[2], _mm_andnot_si128(row[3], row[4])),
            _mm_xor_si128(row[3], _mm_andnot_si128(row[4], row[0])),
            _mm_xor_si128(row[4], _mm_andnot_si128(row[0], row[1])),
        ]
    }
}

#[inline(always)]
fn chi(state: [[__m128i; 5]; 5]) -> [[__m128i; 5]; 5] {
    [
        chi_row(state[0]),
        chi_row(state[1]),
        chi_row(state[2]),
        chi_row(state[3]),
        chi_row(state[4]),
    ]
}

#[inline(always)]
fn iota(i: usize, state: [[__m128i; 5]; 5]) -> [[__m128i; 5]; 5] {
    let mut res = state;
    unsafe {
        res[0][0] = _mm_xor_si128(state[0][0], RC[i]);
    }
    res
}

#[inline(always)]
fn round(i: usize, state: [__m128i; 25]) -> [__m128i; 25] {
    let mut state = form_matrix(state);
    state = theta(state);
    state = rho(state);
    state = pi(state);
    state = chi(state);
    state = iota(i, state);
    flatten(state)
}

fn keccak_perm(buf: &mut [[u64; VECTOR_LEN]; 25]) {
    let mut state: [__m128i; 25] = unsafe { transmute(*buf) };
    for i in 0..24 {
        state = round(i, state);
    }
    *buf = unsafe { transmute::<[__m128i; 25], [[u64; VECTOR_LEN]; 25]>(state) };
}

impl Permutation<[[u64; VECTOR_LEN]; 25]> for KeccakF {
    fn permute_mut(&self, state: &mut [[u64; VECTOR_LEN]; 25]) {
        keccak_perm(state);
    }
}

impl CryptographicPermutation<[[u64; VECTOR_LEN]; 25]> for KeccakF {}

#[cfg(test)]
mod tests {
    use tiny_keccak::keccakf;

    use super::*;

    const STATES: [[u64; 25]; 2] = [
        [
            0xc22c4c11dbedc46a,
            0x317f74268c4f5cd0,
            0x838719da5aa295b6,
            0x9e9b17211985a3ba,
            0x92927b963ce29d69,
            0xf9a7169e38cc7216,
            0x639a594d6fbfe341,
            0x2335ebd8d15777bd,
            0x44e1abc0d022823b,
            0xb3657f9d16b36c13,
            0x26d9217c32b3010a,
            0x6e73d6e9c7e5bcc8,
            0x400aa469d130a391,
            0x1aa7c8a2cb97188a,
            0xdc3084a09bd0a6e3,
            0xbcfe3b656841baea,
            0x325f41887c840166,
            0x844656e313674bfe,
            0xd63de8bad19d156c,
            0x49ef0ac0ab52e147,
            0x8b92ee811c654ca9,
            0x42a9310fedf09bda,
            0x182dbdac03a5358e,
            0x3b4692ce58af8cb5,
            0x534da610f01b8fb3,
        ],
        [
            0x1c322ff4aea07d26,
            0xbd67bde061c97612,
            0x517565bd02ab410a,
            0xb251273ddc12a725,
            0x24f0979fe4f4fedc,
            0xc32d063a64f0bf03,
            0xd33c6709a7b103d2,
            0xaf33a8224b5c8828,
            0x6544ca066e997f1c,
            0xd53ad41e39f06d68,
            0x67695f6fb71d77d9,
            0xd6378cf19ee510f2,
            0x49472ea57abcbd08,
            0xcf3739df1eefbbb4,
            0x0fac1bf30e8ef101,
            0x7ff04c9b90de0f27,
            0xf3d63ec0e64cb2ab,
            0x76388c05f377d4bd,
            0x7886dd8f5b14ef5b,
            0xb036d289ba24a513,
            0x011e8fd6be65a408,
            0x695e2d20848eec67,
            0x31f9e80c5f45f8ee,
            0xcdf873daf7a5fdeb,
            0xfe98ff5bf28d560a,
        ],
    ];

    #[allow(clippy::needless_range_loop)]
    fn our_res() -> [[u64; 25]; 2] {
        let mut packed_result = [[0; 2]; 25];
        for i in 0..25 {
            packed_result[i] = [STATES[0][i], STATES[1][i]];
        }

        keccak_perm(&mut packed_result);

        let mut result = [[0; 25]; 2];
        for i in 0..25 {
            result[0][i] = packed_result[i][0];
            result[1][i] = packed_result[i][1];
        }
        result
    }

    fn tiny_keccak_res() -> [[u64; 25]; 2] {
        let mut result = STATES;
        keccakf(&mut result[0]);
        keccakf(&mut result[1]);
        result
    }

    #[test]
    fn test_vs_tiny_keccak() {
        let expected = tiny_keccak_res();
        let computed = our_res();
        assert_eq!(expected, computed);
    }
}
