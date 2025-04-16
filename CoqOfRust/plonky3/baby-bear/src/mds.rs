//! MDS matrices over the BabyBear field, and permutations defined by them.
//!
//! NB: Not all sizes have fast implementations of their permutations.
//! Supported sizes: 8, 12, 16, 24, 32, 64.
//! Sizes 8 and 12 are from Plonky2, size 16 was found as part of concurrent
//! work by Angus Gruen and Hamish Ivey-Law. Other sizes are from Ulrich Haböck's
//! database.

use p3_mds::util::first_row_to_first_col;
use p3_monty_31::{MDSUtils, MdsMatrixMontyField31};

#[derive(Clone, Default)]
pub struct MDSBabyBearData;

impl MDSUtils for MDSBabyBearData {
    const MATRIX_CIRC_MDS_8_COL: [i64; 8] = first_row_to_first_col(&[7, 1, 3, 8, 8, 3, 4, 9]);
    const MATRIX_CIRC_MDS_12_COL: [i64; 12] =
        first_row_to_first_col(&[1, 1, 2, 1, 8, 9, 10, 7, 5, 9, 4, 10]);
    const MATRIX_CIRC_MDS_16_COL: [i64; 16] =
        first_row_to_first_col(&[1, 1, 51, 1, 11, 17, 2, 1, 101, 63, 15, 2, 67, 22, 13, 3]);
    const MATRIX_CIRC_MDS_24_COL: [i64; 24] = first_row_to_first_col(&[
        0x2D0AAAAB, 0x64850517, 0x17F5551D, 0x04ECBEB5, 0x6D91A8D5, 0x60703026, 0x18D6F3CA,
        0x729601A7, 0x77CDA9E2, 0x3C0F5038, 0x26D52A61, 0x0360405D, 0x68FC71C8, 0x2495A71D,
        0x5D57AFC2, 0x1689DD98, 0x3C2C3DBE, 0x0C23DC41, 0x0524C7F2, 0x6BE4DF69, 0x0A6E572C,
        0x5C7790FA, 0x17E118F6, 0x0878A07F,
    ]);
    const MATRIX_CIRC_MDS_32_COL: [i64; 32] = first_row_to_first_col(&[
        0x0BC00000, 0x2BED8F81, 0x337E0652, 0x4C4535D1, 0x4AF2DC32, 0x2DB4050F, 0x676A7CE3,
        0x3A06B68E, 0x5E95C1B1, 0x2C5F54A0, 0x2332F13D, 0x58E757F1, 0x3AA6DCCE, 0x607EE630,
        0x4ED57FF0, 0x6E08555B, 0x4C155556, 0x587FD0CE, 0x462F1551, 0x032A43CC, 0x5E2E43EA,
        0x71609B02, 0x0ED97E45, 0x562CA7E9, 0x2CB70B1D, 0x4E941E23, 0x174A61C1, 0x117A9426,
        0x73562137, 0x54596086, 0x487C560B, 0x68A4ACAB,
    ]);
    const MATRIX_CIRC_MDS_64_COL: [i64; 64] = first_row_to_first_col(&[
        0x39577778, 0x0072F4E1, 0x0B1B8404, 0x041E9C88, 0x32D22F9F, 0x4E4BF946, 0x20C7B6D7,
        0x0587C267, 0x55877229, 0x4D186EC4, 0x4A19FD23, 0x1A64A20F, 0x2965CA4D, 0x16D98A5A,
        0x471E544A, 0x193D5C8B, 0x6E66DF0C, 0x28BF1F16, 0x26DB0BC8, 0x5B06CDDB, 0x100DCCA2,
        0x65C268AD, 0x199F09E7, 0x36BA04BE, 0x06C393F2, 0x51B06DFD, 0x6951B0C4, 0x6683A4C2,
        0x3B53D11B, 0x26E5134C, 0x45A5F1C5, 0x6F4D2433, 0x3CE2D82E, 0x36309A7D, 0x3DD9B459,
        0x68051E4C, 0x5C3AA720, 0x11640517, 0x0634D995, 0x1B0F6406, 0x72A18430, 0x26513CC5,
        0x67C0B93C, 0x548AB4A3, 0x6395D20D, 0x3E5DBC41, 0x332AF630, 0x3C5DDCB3, 0x0AA95792,
        0x66EB5492, 0x3F78DDDC, 0x5AC41627, 0x16CD5124, 0x3564DA96, 0x461867C9, 0x157B4E11,
        0x1AA486C8, 0x0C5095A9, 0x3833C0C6, 0x008FEBA5, 0x52ECBE2E, 0x1D178A67, 0x58B3C04B,
        0x6E95CB51,
    ]);
}

pub type MdsMatrixBabyBear = MdsMatrixMontyField31<MDSBabyBearData>;

#[cfg(test)]
mod tests {
    use p3_symmetric::Permutation;

    use super::MdsMatrixBabyBear;
    use crate::BabyBear;

    #[test]
    fn babybear8() {
        let input: [BabyBear; 8] = BabyBear::new_array([
            391474477, 1174409341, 666967492, 1852498830, 1801235316, 820595865, 585587525,
            1348326858,
        ]);

        let mds_matrix_baby_bear: MdsMatrixBabyBear = Default::default();

        let output = mds_matrix_baby_bear.permute(input);

        let expected: [BabyBear; 8] = BabyBear::new_array([
            1752937716, 1801468855, 1102954394, 284747746, 1636355768, 205443234, 1235359747,
            1159982032,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn babybear12() {
        let input: [BabyBear; 12] = BabyBear::new_array([
            918423259, 673549090, 364157140, 9832898, 493922569, 1171855651, 246075034, 1542167926,
            1787615541, 1696819900, 1884530130, 422386768,
        ]);

        let mds_matrix_baby_bear: MdsMatrixBabyBear = Default::default();

        let output = mds_matrix_baby_bear.permute(input);

        let expected: [BabyBear; 12] = BabyBear::new_array([
            1631062293, 890348490, 1304705406, 1888740923, 845648570, 717048224, 1082440815,
            914769887, 1872991191, 1366539339, 1805116914, 1998032485,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn babybear16() {
        let input: [BabyBear; 16] = BabyBear::new_array([
            1983708094, 1477844074, 1638775686, 98517138, 70746308, 968700066, 275567720,
            1359144511, 960499489, 1215199187, 474302783, 79320256, 1923147803, 1197733438,
            1638511323, 303948902,
        ]);

        let mds_matrix_baby_bear: MdsMatrixBabyBear = Default::default();

        let output = mds_matrix_baby_bear.permute(input);

        let expected: [BabyBear; 16] = BabyBear::new_array([
            1497569692, 1038070871, 669165859, 456905446, 1116763366, 1267622262, 1985953057,
            1060497461, 704264985, 306103349, 1271339089, 1551541970, 1796459417, 889229849,
            1731972538, 439594789,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn babybear24() {
        let input: [BabyBear; 24] = BabyBear::new_array([
            1307148929, 1603957607, 1515498600, 1412393512, 785287979, 988718522, 1750345556,
            853137995, 534387281, 930390055, 1600030977, 903985158, 1141020507, 636889442,
            966037834, 1778991639, 1440427266, 1379431959, 853403277, 959593575, 733455867,
            908584009, 817124993, 418826476,
        ]);

        let mds_matrix_baby_bear: MdsMatrixBabyBear = Default::default();

        let output = mds_matrix_baby_bear.permute(input);

        let expected: [BabyBear; 24] = BabyBear::new_array([
            1537871777, 1626055274, 1705000179, 1426678258, 1688760658, 1347225494, 1291221794,
            1224656589, 1791446853, 1978133881, 1820380039, 1366829700, 27479566, 409595531,
            1223347944, 1752750033, 594548873, 1447473111, 1385412872, 1111945102, 1366585917,
            138866947, 1326436332, 656898133,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn babybear32() {
        let input: [BabyBear; 32] = BabyBear::new_array([
            1346087634, 1511946000, 1883470964, 54906057, 233060279, 5304922, 1881494193,
            743728289, 404047361, 1148556479, 144976634, 1726343008, 29659471, 1350407160,
            1636652429, 385978955, 327649601, 1248138459, 1255358242, 84164877, 1005571393,
            1713215328, 72913800, 1683904606, 904763213, 316800515, 656395998, 788184609,
            1824512025, 1177399063, 1358745087, 444151496,
        ]);

        let mds_matrix_baby_bear: MdsMatrixBabyBear = Default::default();

        let output = mds_matrix_baby_bear.permute(input);

        let expected: [BabyBear; 32] = BabyBear::new_array([
            1359576919, 1657405784, 1031581836, 212090105, 699048671, 877916349, 205627787,
            1211567750, 210807569, 1696391051, 558468987, 161148427, 304343518, 76611896,
            532792005, 1963649139, 1283500358, 250848292, 1109842541, 2007388683, 433801252,
            1189712914, 626158024, 1436409738, 456315160, 1836818120, 1645024941, 925447491,
            1599571860, 1055439714, 353537136, 379644130,
        ]);

        assert_eq!(output, expected);
    }

    #[test]
    fn babybear64() {
        let input: [BabyBear; 64] = BabyBear::new_array([
            1931358930, 1322576114, 1658000717, 134388215, 1517892791, 1486447670, 93570662,
            898466034, 1576905917, 283824713, 1433559150, 1730678909, 155340881, 1978472263,
            1980644590, 1814040165, 654743892, 849954227, 323176597, 146970735, 252703735,
            1856579399, 162749290, 986745196, 352038183, 1239527508, 828473247, 1184743572,
            1017249065, 36804843, 1378131210, 1286724687, 596095979, 1916924908, 528946791,
            397247884, 23477278, 299412064, 415288430, 935825754, 1218003667, 1954592289,
            1594612673, 664096455, 958392778, 497208288, 1544504580, 1829423324, 956111902,
            458327015, 1736664598, 430977734, 599887171, 1100074154, 1197653896, 427838651,
            466509871, 1236918100, 940670246, 1421951147, 255557957, 1374188100, 315300068,
            623354170,
        ]);

        let mds_matrix_baby_bear: MdsMatrixBabyBear = Default::default();

        let output = mds_matrix_baby_bear.permute(input);

        let expected: [BabyBear; 64] = BabyBear::new_array([
            442300274, 756862170, 167612495, 1103336044, 546496433, 1211822920, 329094196,
            1334376959, 944085937, 977350947, 1445060130, 918469957, 800346119, 1957918170,
            739098112, 1862817833, 1831589884, 1673860978, 698081523, 1128978338, 387929536,
            1106772486, 1367460469, 1911237185, 362669171, 819949894, 1801786287, 1943505026,
            586738185, 996076080, 1641277705, 1680239311, 1005815192, 63087470, 593010310,
            364673774, 543368618, 1576179136, 47618763, 1990080335, 1608655220, 499504830,
            861863262, 765074289, 139277832, 1139970138, 1510286607, 244269525, 43042067,
            119733624, 1314663255, 893295811, 1444902994, 914930267, 1675139862, 1148717487,
            1601328192, 534383401, 296215929, 1924587380, 1336639141, 34897994, 2005302060,
            1780337352,
        ]);

        assert_eq!(output, expected);
    }
}
