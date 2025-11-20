//! An AIR with specified interactions can be augmented into a RAP.
//! This module auto-converts any [Air] implemented on an [InteractionBuilder] into a [Rap].

use p3_air::{Air, AirBuilder};

use super::{InteractionBuilder, RapPhaseSeqKind, SymbolicInteraction};
use crate::{
    interaction::fri_log_up::eval_fri_log_up_phase,
    rap::{PermutationAirBuilderWithExposedValues, Rap},
};

/// Used internally to select RAP phase evaluation function.
pub(crate) trait InteractionPhaseAirBuilder: InteractionBuilder {
    fn finalize_interactions(&mut self);
    /// The symbolic interactions **must** correspond to the `InteractionBuilder::all_interactions` function.
    fn symbolic_interactions(&self) -> Vec<SymbolicInteraction<<Self as AirBuilder>::F>>;
    /// The maximum constraint degree allowed in a RAP.
    fn max_constraint_degree(&self) -> usize;
    fn rap_phase_seq_kind(&self) -> RapPhaseSeqKind;
}

impl<AB, A> Rap<AB> for A
where
    A: Air<AB>,
    AB: InteractionBuilder + PermutationAirBuilderWithExposedValues + InteractionPhaseAirBuilder,
{
    fn eval(&self, builder: &mut AB) {
        // Constraints for the main trace:
        Air::eval(self, builder);
        builder.finalize_interactions();
        if builder.num_interactions() != 0 {
            match builder.rap_phase_seq_kind() {
                RapPhaseSeqKind::FriLogUp => {
                    let symbolic_interactions = builder.symbolic_interactions();
                    eval_fri_log_up_phase(
                        builder,
                        &symbolic_interactions,
                        builder.max_constraint_degree(),
                    );
                }
            }
        }
    }
}
