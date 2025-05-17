//! MDS matrices over the Goldilocks field, and permutations defined by them.
//!
//! NB: Not all sizes have fast implementations of their permutations.
//! Supported sizes: 8, 12, 16, 24, 32, 64, 68.
//! Sizes 8 and 12 are from Plonky2, size 16 was found as part of concurrent
//! work by Angus Gruen and Hamish Ivey-Law. Other sizes are from Ulrich Haböck's
//! database.

use p3_dft::Radix2Bowers;
use p3_mds::MdsPermutation;
use p3_mds::karatsuba_convolution::Convolve;
use p3_mds::util::{apply_circulant, apply_circulant_fft, first_row_to_first_col};
use p3_symmetric::Permutation;

use crate::{Goldilocks, reduce128};

#[derive(Clone, Debug, Default)]
pub struct MdsMatrixGoldilocks;

/// Instantiate convolution for "small" RHS vectors over Goldilocks.
///
/// Here "small" means N = len(rhs) <= 16 and sum(r for r in rhs) <
/// 2^51, though in practice the sum will be less than 2^9.
#[derive(Debug)]
pub struct SmallConvolveGoldilocks;
impl Convolve<Goldilocks, i128, i64, i128> for SmallConvolveGoldilocks {
    /// Return the lift of a Goldilocks element, 0 <= input.value <= P
    /// < 2^64. We widen immediately, since some valid Goldilocks elements
    /// don't fit in an i64, and since in any case overflow can occur
    /// for even the smallest convolutions.
    #[inline(always)]
    fn read(input: Goldilocks) -> i128 {
        input.value as i128
    }

    /// For a convolution of size N, |x| < N * 2^64 and (as per the
    /// assumption above), |y| < 2^51. So the product is at most N *
    /// 2^115 which will not overflow for N <= 16. We widen `y` at
    /// this point to perform the multiplication.
    #[inline(always)]
    fn parity_dot<const N: usize>(u: [i128; N], v: [i64; N]) -> i128 {
        let mut s = 0i128;
        for i in 0..N {
            s += u[i] * v[i] as i128;
        }
        s
    }

    /// The assumptions above mean z < N^2 * 2^115, which is at most
    /// 2^123 when N <= 16.
    ///
    /// NB: Even though intermediate values could be negative, the
    /// output must be non-negative since the inputs were
    /// non-negative.
    #[inline(always)]
    fn reduce(z: i128) -> Goldilocks {
        debug_assert!(z >= 0);
        reduce128(z as u128)
    }
}

const FFT_ALGO: Radix2Bowers = Radix2Bowers;

pub(crate) const MATRIX_CIRC_MDS_8_SML_ROW: [i64; 8] = [7, 1, 3, 8, 8, 3, 4, 9];

impl Permutation<[Goldilocks; 8]> for MdsMatrixGoldilocks {
    fn permute(&self, input: [Goldilocks; 8]) -> [Goldilocks; 8] {
        const MATRIX_CIRC_MDS_8_SML_COL: [i64; 8] =
            first_row_to_first_col(&MATRIX_CIRC_MDS_8_SML_ROW);
        SmallConvolveGoldilocks::apply(
            input,
            MATRIX_CIRC_MDS_8_SML_COL,
            SmallConvolveGoldilocks::conv8,
        )
    }

    fn permute_mut(&self, input: &mut [Goldilocks; 8]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Goldilocks, 8> for MdsMatrixGoldilocks {}

pub(crate) const MATRIX_CIRC_MDS_12_SML_ROW: [i64; 12] = [1, 1, 2, 1, 8, 9, 10, 7, 5, 9, 4, 10];

impl Permutation<[Goldilocks; 12]> for MdsMatrixGoldilocks {
    fn permute(&self, input: [Goldilocks; 12]) -> [Goldilocks; 12] {
        const MATRIX_CIRC_MDS_12_SML_COL: [i64; 12] =
            first_row_to_first_col(&MATRIX_CIRC_MDS_12_SML_ROW);
        SmallConvolveGoldilocks::apply(
            input,
            MATRIX_CIRC_MDS_12_SML_COL,
            SmallConvolveGoldilocks::conv12,
        )
    }

    fn permute_mut(&self, input: &mut [Goldilocks; 12]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Goldilocks, 12> for MdsMatrixGoldilocks {}

pub(crate) const MATRIX_CIRC_MDS_16_SML_ROW: [i64; 16] =
    [1, 1, 51, 1, 11, 17, 2, 1, 101, 63, 15, 2, 67, 22, 13, 3];

impl Permutation<[Goldilocks; 16]> for MdsMatrixGoldilocks {
    fn permute(&self, input: [Goldilocks; 16]) -> [Goldilocks; 16] {
        const MATRIX_CIRC_MDS_16_SML_COL: [i64; 16] =
            first_row_to_first_col(&MATRIX_CIRC_MDS_16_SML_ROW);
        SmallConvolveGoldilocks::apply(
            input,
            MATRIX_CIRC_MDS_16_SML_COL,
            SmallConvolveGoldilocks::conv16,
        )
    }

    fn permute_mut(&self, input: &mut [Goldilocks; 16]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Goldilocks, 16> for MdsMatrixGoldilocks {}

#[rustfmt::skip]
pub(crate) const MATRIX_CIRC_MDS_24_GOLDILOCKS: [u64; 24] = [
    0x5FFFFFFFA00AAAAB, 0x24021AB75BBFE656, 0x7BE9082D73B06DF5, 0x2282863E9C3A5A62,
    0xE0071C70DFFC71C8, 0x796CB65AB42A1A63, 0xDBBBBFFADFFDDDE3, 0x23B88EE217C5C9C2,
    0x20030C309FFB6DB7, 0x23C3C64763BE1E1D, 0x0F93B7C9CC51362E, 0xC697A1094BD0850A,
    0xDFFFFFFF1FFC71C8, 0xC15A4FD614950302, 0xC41D883A4C4DEDF2, 0x187879BC23C46462,
    0x5FFCF3CEDFFE79E8, 0x1C41DF105B82398E, 0x64444003DFFDDDDA, 0x76EDDBB6F7E51F95,
    0x1FF8E38E20038E39, 0x214139BD5C40A09D, 0x3065B7CCF3B3B621, 0x23B6F4622485CEDC,
];

impl Permutation<[Goldilocks; 24]> for MdsMatrixGoldilocks {
    fn permute(&self, input: [Goldilocks; 24]) -> [Goldilocks; 24] {
        apply_circulant(&MATRIX_CIRC_MDS_24_GOLDILOCKS, input)
    }

    fn permute_mut(&self, input: &mut [Goldilocks; 24]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Goldilocks, 24> for MdsMatrixGoldilocks {}

#[rustfmt::skip]
const MATRIX_CIRC_MDS_32_GOLDILOCKS: [u64; 32] = [
    0x0800000000000000, 0x69249248B4924925, 0x3ABD5EAF15EAF57B, 0x294A5294739CE73A,
    0x59E2D2CEB4B3C5A6, 0x087FBE00FF7C0220, 0xA554AA94A554AA96, 0xF00080FEFFDF8005,
    0x64CCCCCC6666699A, 0x5B13AD8973B139D9, 0xAD4A55ACA54AD5AA, 0xDA496DA3B492DB8A,
    0x4AD696955A5694B5, 0xA4A6B29A25B496D3, 0xA74EA162162BD3A9, 0xC698B3A5662CE98C,
    0xA7FFFFFF55555556, 0x4AAAAAAA5AAAAAAB, 0xB047DC113DC11F71, 0x8BA2E8B99B26C9B3,
    0xD259696C5A5B4D2E, 0xA7D540AA557EA9F6, 0x8B6E922D26DB249C, 0xFAAA805455602AAD,
    0xCB33333266666334, 0xD13B17619B13B277, 0x45B26D9326E9374A, 0x52AB552A5AA9556B,
    0x68ED2D2DB4B87697, 0x8B264C98A74E9D3B, 0x09EC23D83D847B09, 0x2C9A4D26669349A5,
];

impl Permutation<[Goldilocks; 32]> for MdsMatrixGoldilocks {
    fn permute(&self, input: [Goldilocks; 32]) -> [Goldilocks; 32] {
        const ENTRIES: [u64; 32] = first_row_to_first_col(&MATRIX_CIRC_MDS_32_GOLDILOCKS);
        apply_circulant_fft(FFT_ALGO, ENTRIES, &input)
    }

    fn permute_mut(&self, input: &mut [Goldilocks; 32]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Goldilocks, 32> for MdsMatrixGoldilocks {}

#[rustfmt::skip]
const MATRIX_CIRC_MDS_64_GOLDILOCKS: [u64; 64] = [
    0x07FFFFFFFC000000, 0xFBFFFFFF04000001, 0x436DB6DB25B6DB6E, 0x4AAAAAAA5AAAAAAB,
    0x45B2D96C6D96CB66, 0x3BC7BC7B87BC7BC8, 0x6318C63125294A53, 0xCB3672CCCD9CB368,
    0xB43CB5A12D68796C, 0xFBFBFBFAFBFBFBFD, 0x883DBF107B7E2210, 0x8A7689B59B629DA3,
    0xF7FEFFDF00000001, 0x7B7C83BBC83BC47C, 0xEFF0410107EF7F83, 0x2CD8B3629CB272CA,
    0x9800019900CCCE67, 0xFBFFFBFF07FFFC01, 0x94EC4A758C4EC628, 0xDA5A5B4A6D2D2E1F,
    0xFFEFC080FC003FFF, 0xBC387BC2C783BC79, 0xB492DB686D24B6F3, 0x1DB6925B4B6E2477,
    0x7801E0EF87BFFF10, 0xFC0803FAFBFC0409, 0x3780FE03C086F21C, 0x8B749B224DB22D94,
    0x32648B36B76E9923, 0x3BC3C3C387C3C3C4, 0x79AF286B4FCA1AF3, 0x9E2762758B627628,
    0x52AAAAAA56AAAAAB, 0xFBFFFFFEFC000001, 0xF7FFFFFF08000001, 0x2CCCCCCC9CCCCCCD,
    0xCF286BC946BCA1B0, 0xBC483B7B883B7C49, 0xD9364D9287C1F07D, 0xAD5A94A8A95AD5AA,
    0xFF871002C400F1E1, 0xFC03FC02FC03FC05, 0xD29495A4D6D4B4A6, 0x6C926DD1DD24DB65,
    0x1EDC247B4DB64937, 0x7C7B843B47BC437D, 0xA55A95AAAD5AD52C, 0x4A96D5A45AD694A6,
    0xFE6664CBCD999801, 0xFC0003FF08000401, 0x1EC4F09D64EC4D8A, 0x9E1E1D2C8B4B4A5B,
    0xD9270937709B64DC, 0x3BB77C4448843B78, 0xFFFFFFDF03FF0021, 0x59D8761D2D8A6299,
    0xC3496878A5E5A4B5, 0xFBF80402FC0403F9, 0x5ECD9B360E142851, 0x6D925D6429D64976,
    0xA8AE615C19CC2B99, 0xBC44444388444445, 0xDFE3F1F81CFC7E40, 0xDA4924916D24924A,
];

impl Permutation<[Goldilocks; 64]> for MdsMatrixGoldilocks {
    fn permute(&self, input: [Goldilocks; 64]) -> [Goldilocks; 64] {
        const ENTRIES: [u64; 64] = first_row_to_first_col(&MATRIX_CIRC_MDS_64_GOLDILOCKS);
        apply_circulant_fft(FFT_ALGO, ENTRIES, &input)
    }

    fn permute_mut(&self, input: &mut [Goldilocks; 64]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Goldilocks, 64> for MdsMatrixGoldilocks {}

#[rustfmt::skip]
const MATRIX_CIRC_MDS_68_GOLDILOCKS: [u64; 68] = [
    0x03C3C3C3FC3C3C3C, 0x6799AFC54A69BC7D, 0xDA8C2C496A74B03B, 0x1E641D7AB35ED229,
    0x9239DA20DA3A2686, 0x6E23D41459EBA8C4, 0x7BC412896E2A6B3A, 0x9082059089ABD4FC,
    0x94A16FA8B0339EEE, 0x85650EC91BB519C9, 0x1600745267E94DE1, 0xFFFD8405C82020AB,
    0x21BDE80429DCED6A, 0x8ACE123AF754E343, 0xFFC7211605D2BDAE, 0xC21187AE15900F4D,
    0x9C4A889708568DC6, 0x65A5A726B5758D8E, 0x949DB90B9AC0D11A, 0x23B6CF7C368BBE52,
    0xD5128DDF59CB5A35, 0xF53BCC5BDADF3A0A, 0xBA7C5112F4BAB1CD, 0x4B93989C5B729351,
    0x6534B7E50E4AD1CB, 0x640061B54C918405, 0x0E66E1F90D2C9311, 0x31C8649B0FE7557F,
    0x0E9190D165F4A8F3, 0x52DF336BB708F919, 0x3C0F6697F14065A5, 0xBE8190942EC50031,
    0x60038E9ACC701118, 0x73F105909A55A88B, 0xFEBEBEBDABEBEBED, 0x6F52163A64B03467,
    0xFBAE131F23A12F56, 0x1950493BC70D0676, 0x2886550DB5A1BBBF, 0x15B003D6E58181D7,
    0x3A4E7D9D44F100F8, 0x6CC3AB896025E6A0, 0x7E23E68456F825E5, 0x079CDD570B591A16,
    0xEC15A830C3D2CCD1, 0xCF4C722D2C0F8A0E, 0xC1BB6F5591B59A26, 0xB63A5931A607BDE0,
    0x43A0AD0B71040187, 0x7E4B492889D1CEE0, 0x734153F3F0C31C5B, 0x98D8D756B2725A5B,
    0x5589D20D74BA00B8, 0xB2DF58DF0A312509, 0xFABC378690D64A3A, 0x700640AFC244B695,
    0xFFA652236547F3BE, 0x2B9CA498A001D059, 0x7DACA6F16787D5DE, 0xAAAD774FAC613EA3,
    0xA88583816975CD56, 0x78B71DC516FF49CA, 0xC7BF095DF702FFA6, 0x78A60B3F971783B3,
    0xCB158EF40BC75CAC, 0xA97E818DBC152B4C, 0x9FC8339D415C3999, 0x006A88C0A0D8201C,
];

impl Permutation<[Goldilocks; 68]> for MdsMatrixGoldilocks {
    fn permute(&self, input: [Goldilocks; 68]) -> [Goldilocks; 68] {
        apply_circulant(&MATRIX_CIRC_MDS_68_GOLDILOCKS, input)
    }

    fn permute_mut(&self, input: &mut [Goldilocks; 68]) {
        *input = self.permute(*input);
    }
}
impl MdsPermutation<Goldilocks, 68> for MdsMatrixGoldilocks {}

#[cfg(test)]
mod tests {
    use p3_symmetric::Permutation;

    use super::{Goldilocks, MdsMatrixGoldilocks};

    #[test]
    fn goldilocks8() {
        let input: [Goldilocks; 8] = Goldilocks::new_array([
            2434589605738284713,
            4817685620989478889,
            13397079175138649456,
            11944520631108649751,
            1033251468644039632,
            3092099742268329866,
            7160548811622790454,
            9959569614427134344,
        ]);

        let output = MdsMatrixGoldilocks.permute(input);

        let expected: [Goldilocks; 8] = Goldilocks::new_array([
            16726687146516531007,
            14721040752765534861,
            15566838577475948790,
            9095485010737904250,
            11353934351835864222,
            11056556168691087893,
            4199602889124860181,
            315643510993921470,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn goldilocks12() {
        let input: [Goldilocks; 12] = Goldilocks::new_array([
            14847187883725400244,
            969392934980971521,
            6996647758016470432,
            4674844440624672154,
            264841656685969785,
            1246852265697711623,
            18223868478428473484,
            12122736699239070772,
            11263701854732819430,
            12739925508864285577,
            11648637570857932167,
            14090978315217600393,
        ]);

        let output = MdsMatrixGoldilocks.permute(input);

        let expected: [Goldilocks; 12] = Goldilocks::new_array([
            9322351889214742299,
            8700136572060418355,
            4881757876459003977,
            9899544690241851021,
            480548822895830465,
            5445915149371405525,
            14955363277757168581,
            6672733082273363313,
            190938676320003294,
            1613225933948270736,
            3549006224849989171,
            12169032187873197425,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn goldilocks16() {
        let input: [Goldilocks; 16] = Goldilocks::new_array([
            13216135600341032847,
            15626390207663319651,
            2052474569300149934,
            4375663431730581786,
            16596827905941257435,
            10019626608444427271,
            7831946179065963230,
            17104499871144693506,
            9021930732511690478,
            6899419210615882449,
            8131182521761419514,
            432489675596019804,
            8508050013409958723,
            14134506582804571789,
            13283546413390931641,
            14711125975653831032,
        ]);

        let output = MdsMatrixGoldilocks.permute(input);

        let expected: [Goldilocks; 16] = Goldilocks::new_array([
            9484392671298797780,
            149770626972189150,
            12125722600598304117,
            15945232149672903756,
            13199929870021500593,
            18443980893262804946,
            317150800081307627,
            16910019239751125049,
            1996802739033818490,
            11668458913264624237,
            11078800762167869397,
            13758408662406282356,
            11119677412113674380,
            7344117715971661026,
            4202436890275702092,
            681166793519210465,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn goldilocks24() {
        let input: [Goldilocks; 24] = Goldilocks::new_array([
            11426771245122339662,
            5975488243963332229,
            11441424994503305651,
            5755561333702259678,
            7295454168648181339,
            16724279929816174064,
            32359231037136391,
            3713621595270370753,
            8421765959140936778,
            12370571593326246544,
            8633733294559731287,
            12765436832373161027,
            15606692828890413034,
            8068160018166226874,
            10719661629577139538,
            13036735610140127982,
            10213543772818211674,
            8041886705706266368,
            12022983417703446028,
            4179370708601587579,
            11125302089484330465,
            9904943018174649533,
            16178194376951442671,
            1545799842160818502,
        ]);

        let output = MdsMatrixGoldilocks.permute(input);

        let expected: [Goldilocks; 24] = Goldilocks::new_array([
            18431075688485197060,
            14823984346528185622,
            7262979358411339215,
            14816911393874702213,
            6721523710303409972,
            10829861327716364029,
            2456948878733883601,
            11088379938350287658,
            3820735023521527858,
            9062288923770492958,
            5159244568306327366,
            1401669669887165869,
            11908734248351870182,
            10640195377186320543,
            6552733980894593378,
            17103376282032495459,
            5204287788603805758,
            17783185518697631139,
            9006863878586007300,
            11122535637762904803,
            5271621316102699962,
            9734499541452484536,
            11778274360927642637,
            3217831681350496533,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn goldilocks32() {
        let input: [Goldilocks; 32] = Goldilocks::new_array([
            8401806579759049284,
            14709608922272986544,
            8130995604641968478,
            7833133203357642391,
            10700492548100684406,
            3941105252506602047,
            8122370916776133262,
            15079919378435648206,
            8774521769784086994,
            16794844316583392853,
            9356562741425567167,
            13317198313361936216,
            7187680218428599522,
            16525662096158660997,
            540453741156061014,
            16543585577270698663,
            3802215918136285729,
            11389297895303247764,
            5133769394766075512,
            1057795099426170863,
            18037861421172314665,
            17632255188776359310,
            17616515088477043142,
            13307921676744533876,
            17602277262015191215,
            15819040654617566738,
            11961318546000835928,
            15593174310433874065,
            9152657050882549004,
            4801868480369948110,
            13202076339494141066,
            726396847460932316,
        ]);

        let output = MdsMatrixGoldilocks.permute(input);

        let expected: [Goldilocks; 32] = Goldilocks::new_array([
            1179701925859507209,
            5543239597787055637,
            5978278622530964070,
            3622388166841103287,
            11383243182536830899,
            14719109850604985734,
            17672601866826623850,
            4879627080283827596,
            7556887460241466109,
            9548493506061808122,
            13980851986825291174,
            2029844508485082398,
            10375517623784134775,
            13067093881736606569,
            6446569064196467795,
            15375603814779462714,
            11307946648742033371,
            1593906954637160608,
            5776169226282316678,
            8167048017892669861,
            3954052226208277367,
            9346878497567392707,
            5570872870988220142,
            10792661164389799960,
            17494962593174487938,
            7080549557843445752,
            14059834522311268132,
            17747288366997773235,
            17158122400620315305,
            6816598002359267850,
            12363049840026116993,
            13313901185845854868,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn goldilocks64() {
        let input: [Goldilocks; 64] = Goldilocks::new_array([
            3471075506106776899,
            4817046918282259009,
            3480368692354016145,
            18110937755057600106,
            3130862083451221140,
            15376650156021437015,
            7997596749112997445,
            7742916918728590149,
            421644639408377358,
            2491271421424548020,
            1940196613872160755,
            7152053147988203177,
            13697425352450853423,
            15877844788345672674,
            17787098720906653510,
            6857627524724866519,
            8541180216786820396,
            10769715704553877654,
            9265712399189924160,
            10220120296438955872,
            18201417281995610945,
            6749698931189855822,
            13700000989116811950,
            13205437213697578097,
            10514342943989454609,
            9926015350795325725,
            2289808224483690257,
            12598806357998460973,
            14393945610969324307,
            4744625557965362093,
            2270701163031951561,
            2927942398784334090,
            5250916386894733430,
            4030189910566345872,
            4953663590324639075,
            1241519685782896035,
            8681312160951359069,
            8236353015475387411,
            4972690458759871996,
            1396852754187463352,
            17512022752774329733,
            14009268822557836700,
            1346736409027879377,
            7609463340861239931,
            10701512803758419515,
            5067199073587389986,
            5030018986055211116,
            17692625804700013551,
            9992938630604785132,
            15350127009762647067,
            10247405821493235386,
            15172888833500531069,
            14657693742399622179,
            7391511805216089127,
            2035742693690795598,
            4047216012963057952,
            12602085105939403203,
            16985723692990258059,
            12141021186082151434,
            3174646196626212833,
            16484520987666295947,
            10579720164460442970,
            9596917135039689219,
            13761818390665814258,
        ]);

        let output = MdsMatrixGoldilocks.permute(input);

        let expected: [Goldilocks; 64] = Goldilocks::new_array([
            9158798369861934356,
            9224859686427886689,
            16948559910286211274,
            15765762765140902574,
            16202509467561200764,
            1911749439284071529,
            4607026757869726805,
            8473827004973131317,
            13716800466551879373,
            6670177022201597800,
            17416833238376299449,
            14953676562252669578,
            5828107070718286209,
            17980287408679531241,
            2220583438808757820,
            14564318040622847100,
            3950519594558514416,
            12164610170526828198,
            457385640833960098,
            14068973922383216628,
            9614382247226943793,
            3932756878771319222,
            12728498054939249570,
            9435109056498897661,
            7283114805836756402,
            1720178259138435097,
            11496602000538177285,
            7736206812858942065,
            14289784438950643645,
            12052665489155550962,
            12918409840610303255,
            5224324424989208352,
            7826309014606327907,
            11657314889847733528,
            13899641072303006348,
            7501780959676548477,
            1064261716045449147,
            1487682458939665452,
            10894217148983862136,
            12785338167343566981,
            8043323074629160032,
            10852328074701301213,
            15029722608724150267,
            2611937278660861263,
            13995790409949796943,
            7103138700054564899,
            12756778219044204581,
            4147399997707606088,
            11930966590061754579,
            16708700985380478903,
            2370160521342035603,
            14893791582608133454,
            15313288276425450946,
            16224601303711716386,
            4488931442519177087,
            7443169181907410918,
            12381442753785370161,
            16366345507676500076,
            8097905256807642731,
            8504207502183388457,
            11400931328719780407,
            10879211614969476303,
            7265889003783205111,
            7322738272300165489,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn goldilocks68() {
        let input: [Goldilocks; 68] = Goldilocks::new_array([
            16450563043143968653,
            3688080826640678185,
            133253417037384537,
            17501558583799613353,
            14920674569425704293,
            5030578721963251055,
            9795600398273758687,
            402012644192671817,
            10657312189068414445,
            9508835336085746575,
            16081669758721272608,
            2072823794278273547,
            16831381326702573736,
            11381683312293543190,
            5679539322738625588,
            9346499485038639332,
            15554202803455984983,
            18373955571490331663,
            11323895584334729789,
            16834542679468148445,
            14751528164286075953,
            3755158780970327991,
            12622814707645103582,
            10329238611694882547,
            7642766530280843057,
            4876120096290984742,
            412912224820604426,
            9118233770240274553,
            3626520971021993076,
            10841049054903806738,
            18205546599950141835,
            7198482606375262809,
            17183313930831625294,
            10181033256431249241,
            1061211413812819905,
            3980261141891682525,
            5674176959446948353,
            6062696542969845681,
            3383081006315025715,
            8812665902421024067,
            3093645099818246186,
            16178737149039707082,
            8204245222345541411,
            11072582337937050490,
            17969785901925882398,
            4670890092981706609,
            12537558683977529426,
            12084598516323376868,
            16293685096019175644,
            10117612240421467846,
            17873102395739074620,
            11220493906741851877,
            4632957003022201019,
            12934229307704669322,
            2152792796882257594,
            12521131928134126701,
            17472006670677761650,
            4560570065837283016,
            6315543803073912887,
            4098689719955359793,
            1784883877365258237,
            6837590090927294950,
            2391417016765166652,
            16389291664603960875,
            12285946887702044436,
            7231705445010258971,
            12976071926225281356,
            8829402645443096358,
        ]);

        let output = MdsMatrixGoldilocks.permute(input);

        let expected: [Goldilocks; 68] = Goldilocks::new_array([
            4984914285749049383,
            10397959071664799177,
            3331616814639908945,
            4252459885611162121,
            5517786723806029201,
            1826620401370703815,
            8257849352373689773,
            1722805960790112693,
            17654983138917187833,
            7542660006721409612,
            1970182718241277021,
            12865815507550811641,
            17507096607056552658,
            7988714902687660369,
            150082662759625574,
            17329095993317360383,
            965880604543562997,
            2820931239306841741,
            1980667983336380501,
            3781794112174728826,
            7323192150179872391,
            12243426826276589932,
            315076483410634889,
            3221894784246078707,
            3515955216509190252,
            964376148920419876,
            7679719864273407732,
            2516714701741920303,
            4837221266652621366,
            15301563603415983061,
            10380321314559647625,
            3023678426639670063,
            12020917879204725519,
            10595808165609787680,
            14199186729378048831,
            4520610719509879248,
            9983949546821718635,
            5066092593424854949,
            13843503196305181790,
            14296362815835302652,
            6766348697864530153,
            13804582129741554661,
            8032169955336281598,
            5198513488794721460,
            10613667919514788349,
            7948289550930596506,
            14118391408956101449,
            4356952068887595371,
            709878153008378134,
            17168579964784489802,
            17840495726541494819,
            2710471020841761312,
            9950159372116756450,
            3909574932971200058,
            2430964021804554670,
            6035162446515244642,
            14656543530572478095,
            1539013407173403800,
            4150113154618904744,
            4904646199269229662,
            17257014030727492672,
            3791823431764085889,
            13680668409434600948,
            12367427987617118934,
            12462908457168650050,
            10891613749697412017,
            6867760775372053830,
            12474954319307005079,
        ]);

        assert_eq!(output, expected);
    }
}
