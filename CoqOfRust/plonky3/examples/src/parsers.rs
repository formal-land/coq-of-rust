//! This file contains a collection of Enums which allow a nice command line interface.
//!
//! For each enum, we allow the user to specify the enum either using the whole string or any substring
//! which fully determines the choice. We additionally add a few extra aliases if other natural ones exist.
//!
//! For most of the enums, this allows the user to

use clap::ValueEnum;
use clap::builder::PossibleValue;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum FieldOptions {
    BabyBear,
    KoalaBear,
    Mersenne31,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum ProofOptions {
    Blake3Permutations,
    KeccakFPermutations,
    Poseidon2Permutations,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum DftOptions {
    None,
    Radix2DitParallel,
    RecursiveDft,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum MerkleHashOptions {
    KeccakF,
    Poseidon2,
}

/// Produce a collection of PossibleValue's for an Enum variant.
///
/// We allow any prefix of the full name which uniquely determines the variant.
/// We additionally allow the user to specify a collection of aliases which are
/// not prefixes. For each alias, we also allow any unique prefix of that alias.
///
/// For example, for the `KoalaBear` variant of `FieldOptions`, running
/// `get_aliases("koala-bear", 1, vec![("koalabear", 6), ("kb", 2)])` produces the following set of
/// allowed strings:
///
/// `koala-bear, k, ko, koa, koal, koala, koala-, koala-b, koala-be, koala-bea, koalab, koalabe, koalabea, koalabear, kb`
fn get_aliases(
    base: &'static str,
    min_unique_base_prefix: usize,
    alias: Option<Vec<(&'static str, usize)>>,
) -> PossibleValue {
    match alias {
        None => PossibleValue::new(base)
            .aliases((min_unique_base_prefix..base.len()).map(|i| &base[..i])),
        Some(vec) => PossibleValue::new(base).aliases(
            (min_unique_base_prefix..base.len())
                .map(|i| &base[..i])
                .chain(vec.into_iter().flat_map(|(alias, min_unique)| {
                    (min_unique..alias.len() + 1).map(|i| &alias[..i])
                })),
        ),
    }
}

impl ValueEnum for FieldOptions {
    fn value_variants<'a>() -> &'a [Self] {
        &[Self::BabyBear, Self::KoalaBear, Self::Mersenne31]
    }

    fn to_possible_value(&self) -> Option<PossibleValue> {
        Some(match self {
            Self::BabyBear => get_aliases("baby-bear", 1, Some(vec![("babybear", 5), ("bb", 2)])),
            Self::KoalaBear => {
                get_aliases("koala-bear", 1, Some(vec![("koalabear", 6), ("kb", 2)]))
            }
            Self::Mersenne31 => {
                get_aliases("mersenne-31", 1, Some(vec![("mersenne31", 9), ("m31", 2)]))
            }
        })
    }
}

impl ValueEnum for ProofOptions {
    fn value_variants<'a>() -> &'a [Self] {
        &[
            Self::Blake3Permutations,
            Self::Poseidon2Permutations,
            Self::KeccakFPermutations,
        ]
    }

    fn to_possible_value(&self) -> Option<PossibleValue> {
        Some(match self {
            Self::Blake3Permutations => get_aliases(
                "blake-3-permutations",
                1,
                Some(vec![("blake3-permutations", 6), ("b3", 2)]),
            ),
            Self::KeccakFPermutations => get_aliases(
                "keccak-f-permutations",
                1,
                Some(vec![("keccakf-permutations", 7), ("kf", 2)]),
            ),
            Self::Poseidon2Permutations => get_aliases(
                "poseidon-2-permutations",
                1,
                Some(vec![("poseidon2-permutations", 9), ("p2", 2)]),
            ),
        })
    }
}

impl ValueEnum for DftOptions {
    fn value_variants<'a>() -> &'a [Self] {
        &[Self::Radix2DitParallel, Self::RecursiveDft, Self::None]
    }

    fn to_possible_value(&self) -> Option<PossibleValue> {
        Some(match self {
            Self::RecursiveDft => get_aliases("recursive-dft", 2, Some(vec![("recursivedft", 10)])),
            Self::Radix2DitParallel => get_aliases(
                "radix-2-dit-parallel",
                2,
                Some(vec![("radix2ditparallel", 6), ("parallel", 1)]),
            ),
            Self::None => PossibleValue::new(""),
        })
    }
}

impl ValueEnum for MerkleHashOptions {
    fn value_variants<'a>() -> &'a [Self] {
        &[Self::Poseidon2, Self::KeccakF]
    }

    fn to_possible_value(&self) -> Option<PossibleValue> {
        Some(match self {
            Self::KeccakF => get_aliases("keccak-f", 1, Some(vec![("keccakf", 7), ("kf", 2)])),
            Self::Poseidon2 => {
                get_aliases("poseidon-2", 1, Some(vec![("poseidon2", 9), ("p2", 2)]))
            }
        })
    }
}
