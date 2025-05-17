use p3_field::Field;
use rand::Rng;
use rand::distr::{Distribution, StandardUniform};

/// Round constants for Poseidon2, in a format that's convenient for the AIR.
#[derive(Debug, Clone)]
pub struct RoundConstants<
    F: Field,
    const WIDTH: usize,
    const HALF_FULL_ROUNDS: usize,
    const PARTIAL_ROUNDS: usize,
> {
    pub(crate) beginning_full_round_constants: [[F; WIDTH]; HALF_FULL_ROUNDS],
    pub(crate) partial_round_constants: [F; PARTIAL_ROUNDS],
    pub(crate) ending_full_round_constants: [[F; WIDTH]; HALF_FULL_ROUNDS],
}

impl<F: Field, const WIDTH: usize, const HALF_FULL_ROUNDS: usize, const PARTIAL_ROUNDS: usize>
    RoundConstants<F, WIDTH, HALF_FULL_ROUNDS, PARTIAL_ROUNDS>
{
    pub const fn new(
        beginning_full_round_constants: [[F; WIDTH]; HALF_FULL_ROUNDS],
        partial_round_constants: [F; PARTIAL_ROUNDS],
        ending_full_round_constants: [[F; WIDTH]; HALF_FULL_ROUNDS],
    ) -> Self {
        Self {
            beginning_full_round_constants,
            partial_round_constants,
            ending_full_round_constants,
        }
    }

    pub fn from_rng<R: Rng>(rng: &mut R) -> Self
    where
        StandardUniform: Distribution<F> + Distribution<[F; WIDTH]>,
    {
        Self {
            beginning_full_round_constants: core::array::from_fn(|_| rng.sample(StandardUniform)),
            partial_round_constants: core::array::from_fn(|_| rng.sample(StandardUniform)),
            ending_full_round_constants: core::array::from_fn(|_| rng.sample(StandardUniform)),
        }
    }
}
