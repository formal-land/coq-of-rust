use core::arch::x86_64::{
    __m512i, _mm512_rol_epi64, _mm512_set1_epi64, _mm512_ternarylogic_epi64, _mm512_xor_epi64,
};
use core::mem::transmute;

use p3_symmetric::{CryptographicPermutation, Permutation};

use crate::KeccakF;

pub const VECTOR_LEN: usize = 8;

const RC: [u64; 24] = [
    1u64,
    0x8082u64,
    0x800000000000808au64,
    0x8000000080008000u64,
    0x808bu64,
    0x80000001u64,
    0x8000000080008081u64,
    0x8000000000008009u64,
    0x8au64,
    0x88u64,
    0x80008009u64,
    0x8000000au64,
    0x8000808bu64,
    0x800000000000008bu64,
    0x8000000000008089u64,
    0x8000000000008003u64,
    0x8000000000008002u64,
    0x8000000000000080u64,
    0x800au64,
    0x800000008000000au64,
    0x8000000080008081u64,
    0x8000000000008080u64,
    0x80000001u64,
    0x8000000080008008u64,
];

#[inline(always)]
fn form_matrix(buf: [__m512i; 25]) -> [[__m512i; 5]; 5] {
    unsafe { transmute(buf) }
}

#[inline(always)]
fn flatten(mat: [[__m512i; 5]; 5]) -> [__m512i; 25] {
    unsafe { transmute(mat) }
}

#[inline(always)]
fn get_theta_parities(state: [[__m512i; 5]; 5]) -> [(__m512i, __m512i); 5] {
    unsafe {
        let mut par0 =
            _mm512_ternarylogic_epi64::<0b10010110>(state[0][0], state[1][0], state[2][0]);
        let mut par1 =
            _mm512_ternarylogic_epi64::<0b10010110>(state[0][1], state[1][1], state[2][1]);
        let mut par2 =
            _mm512_ternarylogic_epi64::<0b10010110>(state[0][2], state[1][2], state[2][2]);
        let mut par3 =
            _mm512_ternarylogic_epi64::<0b10010110>(state[0][3], state[1][3], state[2][3]);
        let mut par4 =
            _mm512_ternarylogic_epi64::<0b10010110>(state[0][4], state[1][4], state[2][4]);

        par0 = _mm512_ternarylogic_epi64::<0b10010110>(par0, state[3][0], state[4][0]);
        par1 = _mm512_ternarylogic_epi64::<0b10010110>(par1, state[3][1], state[4][1]);
        par2 = _mm512_ternarylogic_epi64::<0b10010110>(par2, state[3][2], state[4][2]);
        par3 = _mm512_ternarylogic_epi64::<0b10010110>(par3, state[3][3], state[4][3]);
        par4 = _mm512_ternarylogic_epi64::<0b10010110>(par4, state[3][4], state[4][4]);

        [
            (par4, _mm512_rol_epi64::<1>(par1)),
            (par0, _mm512_rol_epi64::<1>(par2)),
            (par1, _mm512_rol_epi64::<1>(par3)),
            (par2, _mm512_rol_epi64::<1>(par4)),
            (par3, _mm512_rol_epi64::<1>(par0)),
        ]
    }
}

#[inline(always)]
fn theta(state: [[__m512i; 5]; 5]) -> [[__m512i; 5]; 5] {
    let theta_parities = get_theta_parities(state);

    unsafe {
        [
            [
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[0][0],
                    theta_parities[0].0,
                    theta_parities[0].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[0][1],
                    theta_parities[1].0,
                    theta_parities[1].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[0][2],
                    theta_parities[2].0,
                    theta_parities[2].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[0][3],
                    theta_parities[3].0,
                    theta_parities[3].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[0][4],
                    theta_parities[4].0,
                    theta_parities[4].1,
                ),
            ],
            [
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[1][0],
                    theta_parities[0].0,
                    theta_parities[0].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[1][1],
                    theta_parities[1].0,
                    theta_parities[1].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[1][2],
                    theta_parities[2].0,
                    theta_parities[2].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[1][3],
                    theta_parities[3].0,
                    theta_parities[3].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[1][4],
                    theta_parities[4].0,
                    theta_parities[4].1,
                ),
            ],
            [
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[2][0],
                    theta_parities[0].0,
                    theta_parities[0].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[2][1],
                    theta_parities[1].0,
                    theta_parities[1].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[2][2],
                    theta_parities[2].0,
                    theta_parities[2].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[2][3],
                    theta_parities[3].0,
                    theta_parities[3].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[2][4],
                    theta_parities[4].0,
                    theta_parities[4].1,
                ),
            ],
            [
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[3][0],
                    theta_parities[0].0,
                    theta_parities[0].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[3][1],
                    theta_parities[1].0,
                    theta_parities[1].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[3][2],
                    theta_parities[2].0,
                    theta_parities[2].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[3][3],
                    theta_parities[3].0,
                    theta_parities[3].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[3][4],
                    theta_parities[4].0,
                    theta_parities[4].1,
                ),
            ],
            [
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[4][0],
                    theta_parities[0].0,
                    theta_parities[0].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[4][1],
                    theta_parities[1].0,
                    theta_parities[1].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[4][2],
                    theta_parities[2].0,
                    theta_parities[2].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[4][3],
                    theta_parities[3].0,
                    theta_parities[3].1,
                ),
                _mm512_ternarylogic_epi64::<0b10010110>(
                    state[4][4],
                    theta_parities[4].0,
                    theta_parities[4].1,
                ),
            ],
        ]
    }
}

#[inline(always)]
fn rho(state: [[__m512i; 5]; 5]) -> [[__m512i; 5]; 5] {
    unsafe {
        [
            [
                state[0][0],
                _mm512_rol_epi64::<1>(state[0][1]),
                _mm512_rol_epi64::<62>(state[0][2]),
                _mm512_rol_epi64::<28>(state[0][3]),
                _mm512_rol_epi64::<27>(state[0][4]),
            ],
            [
                _mm512_rol_epi64::<36>(state[1][0]),
                _mm512_rol_epi64::<44>(state[1][1]),
                _mm512_rol_epi64::<6>(state[1][2]),
                _mm512_rol_epi64::<55>(state[1][3]),
                _mm512_rol_epi64::<20>(state[1][4]),
            ],
            [
                _mm512_rol_epi64::<3>(state[2][0]),
                _mm512_rol_epi64::<10>(state[2][1]),
                _mm512_rol_epi64::<43>(state[2][2]),
                _mm512_rol_epi64::<25>(state[2][3]),
                _mm512_rol_epi64::<39>(state[2][4]),
            ],
            [
                _mm512_rol_epi64::<41>(state[3][0]),
                _mm512_rol_epi64::<45>(state[3][1]),
                _mm512_rol_epi64::<15>(state[3][2]),
                _mm512_rol_epi64::<21>(state[3][3]),
                _mm512_rol_epi64::<8>(state[3][4]),
            ],
            [
                _mm512_rol_epi64::<18>(state[4][0]),
                _mm512_rol_epi64::<2>(state[4][1]),
                _mm512_rol_epi64::<61>(state[4][2]),
                _mm512_rol_epi64::<56>(state[4][3]),
                _mm512_rol_epi64::<14>(state[4][4]),
            ],
        ]
    }
}

#[inline(always)]
fn pi(state: [[__m512i; 5]; 5]) -> [[__m512i; 5]; 5] {
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
fn chi_row(row: [__m512i; 5]) -> [__m512i; 5] {
    unsafe {
        [
            _mm512_ternarylogic_epi64::<0b11010010>(row[0], row[1], row[2]),
            _mm512_ternarylogic_epi64::<0b11010010>(row[1], row[2], row[3]),
            _mm512_ternarylogic_epi64::<0b11010010>(row[2], row[3], row[4]),
            _mm512_ternarylogic_epi64::<0b11010010>(row[3], row[4], row[0]),
            _mm512_ternarylogic_epi64::<0b11010010>(row[4], row[0], row[1]),
        ]
    }
}

#[inline(always)]
fn chi(state: [[__m512i; 5]; 5]) -> [[__m512i; 5]; 5] {
    [
        chi_row(state[0]),
        chi_row(state[1]),
        chi_row(state[2]),
        chi_row(state[3]),
        chi_row(state[4]),
    ]
}

#[inline(always)]
fn iota(i: usize, state: [[__m512i; 5]; 5]) -> [[__m512i; 5]; 5] {
    let mut res = state;
    unsafe {
        res[0][0] = _mm512_xor_epi64(state[0][0], _mm512_set1_epi64(RC[i] as i64));
    }
    res
}
#[inline(always)]
fn round(i: usize, state: [__m512i; 25]) -> [__m512i; 25] {
    let mut state = form_matrix(state);
    state = theta(state);
    state = rho(state);
    state = pi(state);
    state = chi(state);
    state = iota(i, state);
    flatten(state)
}

fn keccak_perm(buf: &mut [[u64; VECTOR_LEN]; 25]) {
    let mut state: [__m512i; 25] = unsafe { transmute(*buf) };
    for i in 0..24 {
        state = round(i, state);
    }
    *buf = unsafe { transmute::<[__m512i; 25], [[u64; VECTOR_LEN]; 25]>(state) };
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

    const STATES: [[u64; 25]; 8] = [
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
        [
            0x3a7a076a7653164a,
            0x831ec41826c9f433,
            0xe741ec156d6cc2e8,
            0x9d22d9b4c52d1fcd,
            0x29378130bb66801f,
            0x7cb8ed48278ca775,
            0xda6eb5186ea6d93a,
            0xcb1af159fddb7de9,
            0x36fcc875105933ec,
            0x769bcf74dfc5633e,
            0x007493ff65d57f29,
            0xf25df62693770de4,
            0xa19106354a107435,
            0x3e22d2a729a5cfc0,
            0x1b668ba97bb34bda,
            0x3431c9e512de7508,
            0xaef52c95d26bee5c,
            0xd469b70970274fac,
            0xacb862720dc53c99,
            0x5611b0fac5ee9c0e,
            0xbd0c97dc9334b4d1,
            0x60f5b3e10a84d18b,
            0xcdc7ce6afa7bb654,
            0xf9718de3fbd9912e,
            0x52cf33b8bc689764,
        ],
        [
            0x05bb9ba0620488de,
            0x255c733bef224059,
            0x836115d2296389ba,
            0x0ab2167d49cb289f,
            0x1e945f1edf1ae30f,
            0x36af6f7dd549671a,
            0xb916e7817d618a31,
            0xacc5e1bc38255a26,
            0x6e30e1996f6ff60d,
            0x444d39f393a03988,
            0x9be737f450a656d1,
            0x54908135176000bb,
            0x22dfe68128bbbd2a,
            0x4538a20e8a41722f,
            0x9300dad7d26702ac,
            0x1ca0e4154cb8fa3c,
            0xe79bd6461d454f8c,
            0x97623f4622fc67f1,
            0xdd34f7723269bec4,
            0x095027718c687fe2,
            0x765164adaf88f509,
            0x10398b41075c534f,
            0xe4f0b2a3dc53fa47,
            0x47d683e87df22978,
            0x977202dbb006d455,
        ],
        [
            0x6de734e9ca9ddca9,
            0x7cc622c3598980d0,
            0x8c70c4f776592af9,
            0x144bf613df515cce,
            0xed86fd2c951c694d,
            0x0a611f64e6cc71c3,
            0xae4f84322fc5998a,
            0xb816fc65939ab4a8,
            0xa577b843b0abd02e,
            0x2160c58bb6db9141,
            0xc265e1147f5acd16,
            0x2e92b214f27e458c,
            0xa3a3ebcd6499c3cf,
            0x7bc8a5d387a5ad1f,
            0xf76dea4bb3417c7a,
            0x6f4363ceac81fb57,
            0x32b5083239511ab5,
            0x9a0d5ab2ce107ca6,
            0x096a14d0969929c3,
            0x584c7db06dff5e95,
            0x8c65e65adf7b69bc,
            0x022d0d01ad78864c,
            0x446e102a8d2bcc57,
            0x2320241b97aadd47,
            0x1f13645237109652,
        ],
        [
            0xe3149e204e6a7aa5,
            0x23897bedb6c59de2,
            0x03f0745c35262f50,
            0x8dcf451d452046ed,
            0xfb287468366762a1,
            0x78985371e9efbf92,
            0x6666bed6730a6dec,
            0xe8558e22c8470063,
            0x21ef2a4bc19dee21,
            0x1ee3471999a6b9d2,
            0x4bf213b0fa5d9543,
            0x58eb13d92e3e3ee0,
            0xe846d822d8c8465f,
            0x8d1651f1bbb16da3,
            0x22ee8e86032c05f9,
            0xcef6a50f4ffb4858,
            0xfcbbb4a9a09bd82a,
            0xa40a08af13eff462,
            0x10dc2712bd87257e,
            0xe62affc17fc01ee6,
            0xecc888362afd5d4c,
            0x8caf7e13b4c630bc,
            0xa6cec6299e0ec6fb,
            0xb876c1f8dd351df4,
            0x9e8edc1e068c2f1c,
        ],
    ];

    #[allow(clippy::needless_range_loop)]
    fn our_res() -> [[u64; 25]; 8] {
        let mut packed_result = [[0; 8]; 25];
        for (i, packed_res) in packed_result.iter_mut().enumerate() {
            *packed_res = [
                STATES[0][i],
                STATES[1][i],
                STATES[2][i],
                STATES[3][i],
                STATES[4][i],
                STATES[5][i],
                STATES[6][i],
                STATES[7][i],
            ];
        }

        keccak_perm(&mut packed_result);

        let mut result = [[0; 25]; 8];
        for (i, packed_res) in packed_result.iter_mut().enumerate() {
            result[0][i] = packed_res[0];
            result[1][i] = packed_res[1];
            result[2][i] = packed_res[2];
            result[3][i] = packed_res[3];
            result[4][i] = packed_res[4];
            result[5][i] = packed_res[5];
            result[6][i] = packed_res[6];
            result[7][i] = packed_res[7];
        }
        result
    }

    fn tiny_keccak_res() -> [[u64; 25]; 8] {
        let mut result = STATES;
        keccakf(&mut result[0]);
        keccakf(&mut result[1]);
        keccakf(&mut result[2]);
        keccakf(&mut result[3]);
        keccakf(&mut result[4]);
        keccakf(&mut result[5]);
        keccakf(&mut result[6]);
        keccakf(&mut result[7]);
        result
    }

    #[test]
    fn test_vs_tiny_keccak() {
        let expected = tiny_keccak_res();
        let computed = our_res();
        assert_eq!(expected, computed);
    }
}
