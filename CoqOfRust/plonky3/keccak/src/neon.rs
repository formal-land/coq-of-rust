use core::arch::aarch64::{uint64x2_t, vbcaxq_u64, veor3q_u64, veorq_u64, vrax1q_u64, vxarq_u64};
use core::mem::transmute;

use p3_symmetric::{CryptographicPermutation, Permutation};

use crate::KeccakF;

pub const VECTOR_LEN: usize = 2;

const RC: [uint64x2_t; 24] = unsafe {
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
fn form_matrix(buf: [uint64x2_t; 25]) -> [[uint64x2_t; 5]; 5] {
    unsafe { transmute(buf) }
}

#[inline(always)]
fn flatten(mat: [[uint64x2_t; 5]; 5]) -> [uint64x2_t; 25] {
    unsafe { transmute(mat) }
}

#[inline(always)]
fn get_theta_parities(state: [[uint64x2_t; 5]; 5]) -> [uint64x2_t; 5] {
    unsafe {
        let mut par0 = veor3q_u64(state[0][0], state[1][0], state[2][0]);
        let mut par1 = veor3q_u64(state[0][1], state[1][1], state[2][1]);
        let mut par2 = veor3q_u64(state[0][2], state[1][2], state[2][2]);
        let mut par3 = veor3q_u64(state[0][3], state[1][3], state[2][3]);
        let mut par4 = veor3q_u64(state[0][4], state[1][4], state[2][4]);

        par0 = veor3q_u64(par0, state[3][0], state[4][0]);
        par1 = veor3q_u64(par1, state[3][1], state[4][1]);
        par2 = veor3q_u64(par2, state[3][2], state[4][2]);
        par3 = veor3q_u64(par3, state[3][3], state[4][3]);
        par4 = veor3q_u64(par4, state[3][4], state[4][4]);

        [
            vrax1q_u64(par4, par1),
            vrax1q_u64(par0, par2),
            vrax1q_u64(par1, par3),
            vrax1q_u64(par2, par4),
            vrax1q_u64(par3, par0),
        ]
    }
}

#[inline(always)]
fn theta_rho(state: [[uint64x2_t; 5]; 5]) -> [[uint64x2_t; 5]; 5] {
    let theta_parities = get_theta_parities(state);

    unsafe {
        [
            [
                veorq_u64(state[0][0], theta_parities[0]),
                vxarq_u64::<63>(state[0][1], theta_parities[1]),
                vxarq_u64::<2>(state[0][2], theta_parities[2]),
                vxarq_u64::<36>(state[0][3], theta_parities[3]),
                vxarq_u64::<37>(state[0][4], theta_parities[4]),
            ],
            [
                vxarq_u64::<28>(state[1][0], theta_parities[0]),
                vxarq_u64::<20>(state[1][1], theta_parities[1]),
                vxarq_u64::<58>(state[1][2], theta_parities[2]),
                vxarq_u64::<9>(state[1][3], theta_parities[3]),
                vxarq_u64::<44>(state[1][4], theta_parities[4]),
            ],
            [
                vxarq_u64::<61>(state[2][0], theta_parities[0]),
                vxarq_u64::<54>(state[2][1], theta_parities[1]),
                vxarq_u64::<21>(state[2][2], theta_parities[2]),
                vxarq_u64::<39>(state[2][3], theta_parities[3]),
                vxarq_u64::<25>(state[2][4], theta_parities[4]),
            ],
            [
                vxarq_u64::<23>(state[3][0], theta_parities[0]),
                vxarq_u64::<19>(state[3][1], theta_parities[1]),
                vxarq_u64::<49>(state[3][2], theta_parities[2]),
                vxarq_u64::<43>(state[3][3], theta_parities[3]),
                vxarq_u64::<56>(state[3][4], theta_parities[4]),
            ],
            [
                vxarq_u64::<46>(state[4][0], theta_parities[0]),
                vxarq_u64::<62>(state[4][1], theta_parities[1]),
                vxarq_u64::<3>(state[4][2], theta_parities[2]),
                vxarq_u64::<8>(state[4][3], theta_parities[3]),
                vxarq_u64::<50>(state[4][4], theta_parities[4]),
            ],
        ]
    }
}

#[inline(always)]
const fn pi(state: [[uint64x2_t; 5]; 5]) -> [[uint64x2_t; 5]; 5] {
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
fn chi_row(row: [uint64x2_t; 5]) -> [uint64x2_t; 5] {
    unsafe {
        [
            vbcaxq_u64(row[0], row[2], row[1]),
            vbcaxq_u64(row[1], row[3], row[2]),
            vbcaxq_u64(row[2], row[4], row[3]),
            vbcaxq_u64(row[3], row[0], row[4]),
            vbcaxq_u64(row[4], row[1], row[0]),
        ]
    }
}

#[inline(always)]
fn chi(state: [[uint64x2_t; 5]; 5]) -> [[uint64x2_t; 5]; 5] {
    [
        chi_row(state[0]),
        chi_row(state[1]),
        chi_row(state[2]),
        chi_row(state[3]),
        chi_row(state[4]),
    ]
}

#[inline(always)]
fn iota(i: usize, state: [[uint64x2_t; 5]; 5]) -> [[uint64x2_t; 5]; 5] {
    let mut res = state;
    unsafe {
        res[0][0] = veorq_u64(state[0][0], RC[i]);
    }
    res
}

#[inline(always)]
fn round(i: usize, state: [uint64x2_t; 25]) -> [uint64x2_t; 25] {
    let mut state = form_matrix(state);
    state = theta_rho(state);
    state = pi(state);
    state = chi(state);
    state = iota(i, state);
    flatten(state)
}

fn keccak_perm(buf: &mut [[u64; VECTOR_LEN]; 25]) {
    let mut state: [uint64x2_t; 25] = unsafe { transmute(*buf) };
    for i in 0..24 {
        state = round(i, state);
    }
    *buf = unsafe { transmute::<[uint64x2_t; 25], [[u64; VECTOR_LEN]; 25]>(state) };
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
