use core::arch::x86_64::{
    __m256i, _mm256_add_epi64, _mm256_andnot_si256, _mm256_or_si256, _mm256_shuffle_epi8,
    _mm256_slli_epi64, _mm256_srli_epi64, _mm256_xor_si256,
};
use core::mem::transmute;

use p3_symmetric::{CryptographicPermutation, Permutation};

use crate::KeccakF;

pub const VECTOR_LEN: usize = 4;

const RC: [__m256i; 24] = unsafe {
    transmute([
        [1u64; 4],
        [0x8082u64; 4],
        [0x800000000000808au64; 4],
        [0x8000000080008000u64; 4],
        [0x808bu64; 4],
        [0x80000001u64; 4],
        [0x8000000080008081u64; 4],
        [0x8000000000008009u64; 4],
        [0x8au64; 4],
        [0x88u64; 4],
        [0x80008009u64; 4],
        [0x8000000au64; 4],
        [0x8000808bu64; 4],
        [0x800000000000008bu64; 4],
        [0x8000000000008089u64; 4],
        [0x8000000000008003u64; 4],
        [0x8000000000008002u64; 4],
        [0x8000000000000080u64; 4],
        [0x800au64; 4],
        [0x800000008000000au64; 4],
        [0x8000000080008081u64; 4],
        [0x8000000000008080u64; 4],
        [0x80000001u64; 4],
        [0x8000000080008008u64; 4],
    ])
};

#[inline(always)]
fn form_matrix(buf: [__m256i; 25]) -> [[__m256i; 5]; 5] {
    unsafe { transmute(buf) }
}

#[inline(always)]
fn flatten(mat: [[__m256i; 5]; 5]) -> [__m256i; 25] {
    unsafe { transmute(mat) }
}

#[inline(always)]
fn rol_1(a: __m256i) -> __m256i {
    unsafe {
        let shl = _mm256_add_epi64(a, a);
        let shr = _mm256_srli_epi64::<63>(a);
        _mm256_or_si256(shl, shr)
    }
}

const ROL_8_CTRL: __m256i = unsafe {
    transmute::<[u8; 32], _>([
        0o07, 0o00, 0o01, 0o02, 0o03, 0o04, 0o05, 0o06, 0o17, 0o10, 0o11, 0o12, 0o13, 0o14, 0o15,
        0o16, 0o07, 0o00, 0o01, 0o02, 0o03, 0o04, 0o05, 0o06, 0o17, 0o10, 0o11, 0o12, 0o13, 0o14,
        0o15, 0o16,
    ])
};

#[inline(always)]
fn rol_8(a: __m256i) -> __m256i {
    unsafe { _mm256_shuffle_epi8(a, ROL_8_CTRL) }
}

const ROL_56_CTRL: __m256i = unsafe {
    transmute::<[u8; 32], _>([
        0o01, 0o02, 0o03, 0o04, 0o05, 0o06, 0o07, 0o00, 0o11, 0o12, 0o13, 0o14, 0o15, 0o16, 0o17,
        0o10, 0o01, 0o02, 0o03, 0o04, 0o05, 0o06, 0o07, 0o00, 0o11, 0o12, 0o13, 0o14, 0o15, 0o16,
        0o17, 0o10,
    ])
};

#[inline(always)]
fn rol_56(a: __m256i) -> __m256i {
    unsafe { _mm256_shuffle_epi8(a, ROL_56_CTRL) }
}

#[inline(always)]
fn rol<const SHL_AMT: i32, const SHR_AMT: i32>(a: __m256i) -> __m256i {
    unsafe {
        let shl = _mm256_slli_epi64::<SHL_AMT>(a);
        let shr = _mm256_srli_epi64::<SHR_AMT>(a);
        _mm256_or_si256(shl, shr)
    }
}

#[inline(always)]
fn get_theta_parities(state: [[__m256i; 5]; 5]) -> [__m256i; 5] {
    unsafe {
        let mut par0 = _mm256_xor_si256(state[0][0], state[1][0]);
        let mut par1 = _mm256_xor_si256(state[0][1], state[1][1]);
        let mut par2 = _mm256_xor_si256(state[0][2], state[1][2]);
        let mut par3 = _mm256_xor_si256(state[0][3], state[1][3]);
        let mut par4 = _mm256_xor_si256(state[0][4], state[1][4]);

        par0 = _mm256_xor_si256(par0, state[2][0]);
        par1 = _mm256_xor_si256(par1, state[2][1]);
        par2 = _mm256_xor_si256(par2, state[2][2]);
        par3 = _mm256_xor_si256(par3, state[2][3]);
        par4 = _mm256_xor_si256(par4, state[2][4]);

        par0 = _mm256_xor_si256(par0, state[3][0]);
        par1 = _mm256_xor_si256(par1, state[3][1]);
        par2 = _mm256_xor_si256(par2, state[3][2]);
        par3 = _mm256_xor_si256(par3, state[3][3]);
        par4 = _mm256_xor_si256(par4, state[3][4]);

        par0 = _mm256_xor_si256(par0, state[4][0]);
        par1 = _mm256_xor_si256(par1, state[4][1]);
        par2 = _mm256_xor_si256(par2, state[4][2]);
        par3 = _mm256_xor_si256(par3, state[4][3]);
        par4 = _mm256_xor_si256(par4, state[4][4]);

        [
            _mm256_xor_si256(par4, rol_1(par1)),
            _mm256_xor_si256(par0, rol_1(par2)),
            _mm256_xor_si256(par1, rol_1(par3)),
            _mm256_xor_si256(par2, rol_1(par4)),
            _mm256_xor_si256(par3, rol_1(par0)),
        ]
    }
}

#[inline(always)]
fn theta(state: [[__m256i; 5]; 5]) -> [[__m256i; 5]; 5] {
    let theta_parities = get_theta_parities(state);

    unsafe {
        [
            [
                _mm256_xor_si256(state[0][0], theta_parities[0]),
                _mm256_xor_si256(state[0][1], theta_parities[1]),
                _mm256_xor_si256(state[0][2], theta_parities[2]),
                _mm256_xor_si256(state[0][3], theta_parities[3]),
                _mm256_xor_si256(state[0][4], theta_parities[4]),
            ],
            [
                _mm256_xor_si256(state[1][0], theta_parities[0]),
                _mm256_xor_si256(state[1][1], theta_parities[1]),
                _mm256_xor_si256(state[1][2], theta_parities[2]),
                _mm256_xor_si256(state[1][3], theta_parities[3]),
                _mm256_xor_si256(state[1][4], theta_parities[4]),
            ],
            [
                _mm256_xor_si256(state[2][0], theta_parities[0]),
                _mm256_xor_si256(state[2][1], theta_parities[1]),
                _mm256_xor_si256(state[2][2], theta_parities[2]),
                _mm256_xor_si256(state[2][3], theta_parities[3]),
                _mm256_xor_si256(state[2][4], theta_parities[4]),
            ],
            [
                _mm256_xor_si256(state[3][0], theta_parities[0]),
                _mm256_xor_si256(state[3][1], theta_parities[1]),
                _mm256_xor_si256(state[3][2], theta_parities[2]),
                _mm256_xor_si256(state[3][3], theta_parities[3]),
                _mm256_xor_si256(state[3][4], theta_parities[4]),
            ],
            [
                _mm256_xor_si256(state[4][0], theta_parities[0]),
                _mm256_xor_si256(state[4][1], theta_parities[1]),
                _mm256_xor_si256(state[4][2], theta_parities[2]),
                _mm256_xor_si256(state[4][3], theta_parities[3]),
                _mm256_xor_si256(state[4][4], theta_parities[4]),
            ],
        ]
    }
}

#[inline(always)]
fn rho(state: [[__m256i; 5]; 5]) -> [[__m256i; 5]; 5] {
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
fn pi(state: [[__m256i; 5]; 5]) -> [[__m256i; 5]; 5] {
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
fn chi_row(row: [__m256i; 5]) -> [__m256i; 5] {
    unsafe {
        [
            _mm256_xor_si256(row[0], _mm256_andnot_si256(row[1], row[2])),
            _mm256_xor_si256(row[1], _mm256_andnot_si256(row[2], row[3])),
            _mm256_xor_si256(row[2], _mm256_andnot_si256(row[3], row[4])),
            _mm256_xor_si256(row[3], _mm256_andnot_si256(row[4], row[0])),
            _mm256_xor_si256(row[4], _mm256_andnot_si256(row[0], row[1])),
        ]
    }
}

#[inline(always)]
fn chi(state: [[__m256i; 5]; 5]) -> [[__m256i; 5]; 5] {
    [
        chi_row(state[0]),
        chi_row(state[1]),
        chi_row(state[2]),
        chi_row(state[3]),
        chi_row(state[4]),
    ]
}

#[inline(always)]
fn iota(i: usize, state: [[__m256i; 5]; 5]) -> [[__m256i; 5]; 5] {
    let mut res = state;
    unsafe {
        res[0][0] = _mm256_xor_si256(state[0][0], RC[i]);
    }
    res
}

#[inline(always)]
fn round(i: usize, state: [__m256i; 25]) -> [__m256i; 25] {
    let mut state = form_matrix(state);
    state = theta(state);
    state = rho(state);
    state = pi(state);
    state = chi(state);
    state = iota(i, state);
    flatten(state)
}

fn keccak_perm(buf: &mut [[u64; VECTOR_LEN]; 25]) {
    let mut state: [__m256i; 25] = unsafe { transmute(*buf) };
    for i in 0..24 {
        state = round(i, state);
    }
    *buf = unsafe { transmute::<[__m256i; 25], [[u64; VECTOR_LEN]; 25]>(state) };
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

    const STATES: [[u64; 25]; 4] = [
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
        [
            0xed7423c3e4cda469,
            0x8bbbe52577993e33,
            0x93182a78487f96db,
            0x3c5209456d78dc73,
            0x8b66bde37b967146,
            0x226ae6e2148314fc,
            0x302aed4f30cd2db9,
            0x621a7c7751302084,
            0x4054874254bc66cc,
            0xb513327739d3c109,
            0x0ae03189599dd81a,
            0x457e6f324e512ed9,
            0x3870ea63c7367728,
            0xb08c7c0e401d2623,
            0xa1316890c9bb3ac1,
            0x0a313e02f34f6c7e,
            0x7c1325754df4dbf5,
            0x287e3d88240bedd2,
            0xc7c0f3c5058290bb,
            0x39471c62d065a4d1,
            0x050d8ecb5c7911bf,
            0x7a6cd7ca757186a7,
            0xed14a51934a17895,
            0x8a75418d7ffb98dd,
            0x8096f8d803188d57,
        ],
        [
            0x118d693606b316cd,
            0xc2614f04c0dfca91,
            0x5eb3da95450a214f,
            0x193eb69a8198e724,
            0xc24dea1c58e5fa6d,
            0xcf8630adb771d47c,
            0xe612253b23ade1df,
            0x281b2b53f2d5fe61,
            0x9a3f8fb149d7c419,
            0x7ac1eeffbd426464,
            0xb1bdb03caa7b20a3,
            0x4e38a03b709d47d1,
            0x35cafd22e9a91879,
            0x26c9ae757c5b9f80,
            0x9113b092720d90db,
            0xeb504ed5104a0a09,
            0x1405c220c45ee2b1,
            0x8055d2c37b02472b,
            0x545eeff9734b4b99,
            0x79eb67721385dff8,
            0x4133f750b0446360,
            0x7167e6c1fd8ff59b,
            0x576436ac7d46936e,
            0x8db22fbb547d0826,
            0xa855d775d64f0110,
        ],
    ];

    #[allow(clippy::needless_range_loop)]
    fn our_res() -> [[u64; 25]; 4] {
        let mut packed_result = [[0; 4]; 25];
        for (i, packed_res) in packed_result.iter_mut().enumerate() {
            *packed_res = [STATES[0][i], STATES[1][i], STATES[2][i], STATES[3][i]];
        }

        keccak_perm(&mut packed_result);

        let mut result = [[0; 25]; 4];
        for (i, packed_res) in packed_result.iter_mut().enumerate() {
            result[0][i] = packed_res[0];
            result[1][i] = packed_res[1];
            result[2][i] = packed_res[2];
            result[3][i] = packed_res[3];
        }
        result
    }

    fn tiny_keccak_res() -> [[u64; 25]; 4] {
        let mut result = STATES;
        keccakf(&mut result[0]);
        keccakf(&mut result[1]);
        keccakf(&mut result[2]);
        keccakf(&mut result[3]);
        result
    }

    #[test]
    fn test_vs_tiny_keccak() {
        let expected = tiny_keccak_res();
        let computed = our_res();
        assert_eq!(expected, computed);
    }
}
