use std::{fmt::Debug, sync::Arc};

use p3_air::AirBuilder;
use p3_challenger::CanObserve;
use p3_field::Field;
use p3_matrix::dense::RowMajorMatrix;
use p3_util::log2_ceil_usize;
use serde::{de::DeserializeOwned, Deserialize, Serialize};

use crate::{
    air_builders::symbolic::{symbolic_expression::SymbolicExpression, SymbolicConstraints},
    interaction::fri_log_up::{STARK_LU_NUM_CHALLENGES, STARK_LU_NUM_EXPOSED_VALUES},
    prover::types::PairView,
};

/// Interaction debugging tools
pub mod debug;
pub mod fri_log_up;
pub mod rap;
pub mod trace;
mod utils;

// Must be a type smaller than u32 to make BusIndex p - 1 unrepresentable.
pub type BusIndex = u16;

#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct Interaction<Expr> {
    pub message: Vec<Expr>,
    pub count: Expr,
    /// The bus index specifying the bus to send the message over. All valid instantiations of
    /// `BusIndex` are safe.
    pub bus_index: BusIndex,
    /// Determines the contribution of each interaction message to a linear constraint on the trace
    /// heights in the verifier.
    ///
    /// For each bus index and trace, `count_weight` values are summed per interaction on that
    /// bus index and multiplied by the trace height. The total sum over all traces is constrained
    /// by the verifier to not overflow the field characteristic \( p \).
    ///
    /// This is used to impose sufficient conditions for bus constraint soundness and setting a
    /// proper value depends on the bus and the constraint it imposes.
    pub count_weight: u32,
}

pub type SymbolicInteraction<F> = Interaction<SymbolicExpression<F>>;

/// An [AirBuilder] with additional functionality to build special logUp arguments for
/// communication between AIRs across buses. These arguments use randomness to
/// add additional trace columns (in the extension field) and constraints to the AIR.
///
/// An interactive AIR is a AIR that can specify buses for sending and receiving data
/// to other AIRs. The original AIR is augmented by virtual columns determined by
/// the interactions to define a [RAP](crate::rap::Rap).
pub trait InteractionBuilder: AirBuilder {
    /// Stores a new interaction in the builder.
    ///
    /// See [Interaction] for more details on `count_weight`.
    fn push_interaction<E: Into<Self::Expr>>(
        &mut self,
        bus_index: BusIndex,
        fields: impl IntoIterator<Item = E>,
        count: impl Into<Self::Expr>,
        count_weight: u32,
    );

    /// Returns the current number of interactions.
    fn num_interactions(&self) -> usize;

    /// Returns all interactions stored.
    fn all_interactions(&self) -> &[Interaction<Self::Expr>];
}

/// A `Lookup` bus is used to establish that one multiset of values (the queries) are subset of
/// another multiset of values (the keys).
///
/// Soundness requires that the total number of queries sent over the bus per message is at most the
/// field characteristic.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct LookupBus {
    pub index: BusIndex,
}

impl LookupBus {
    pub const fn new(index: BusIndex) -> Self {
        Self { index }
    }

    /// Performs a lookup on the given bus.
    ///
    /// This method asserts that `key` is present in the lookup table. The parameter `enabled`
    /// must be constrained to be boolean, and the lookup constraint is imposed provided `enabled`
    /// is one.
    ///
    /// Caller must constrain that `enabled` is boolean.
    pub fn lookup_key<AB, E>(
        &self,
        builder: &mut AB,
        query: impl IntoIterator<Item = E>,
        enabled: impl Into<AB::Expr>,
    ) where
        AB: InteractionBuilder,
        E: Into<AB::Expr>,
    {
        // We embed the query multiplicity as {0, 1} in the integers and the lookup table key
        // multiplicity to be {0, -1, ..., -p + 1}. Setting `count_weight = 1` will ensure that the
        // total number of lookups is at most p, which is sufficient to establish lookup multiset is
        // a subset of the key multiset. See Corollary 3.6 in [docs/Soundess_of_Interactions_via_LogUp.pdf].
        builder.push_interaction(self.index, query, enabled, 1);
    }

    /// Adds a key to the lookup table.
    ///
    /// The `num_lookups` parameter should equal the number of enabled lookups performed.
    pub fn add_key_with_lookups<AB, E>(
        &self,
        builder: &mut AB,
        key: impl IntoIterator<Item = E>,
        num_lookups: impl Into<AB::Expr>,
    ) where
        AB: InteractionBuilder,
        E: Into<AB::Expr>,
    {
        // Since we only want a subset constraint, `count_weight` can be zero here. See the comment
        // in `LookupBus::lookup_key`.
        builder.push_interaction(self.index, key, -num_lookups.into(), 0);
    }
}

/// A `PermutationCheckBus` bus is used to establish that two multi-sets of values are equal.
///
/// Soundness requires that both the total number of messages sent and received over the bus per
/// message is at most the field characteristic.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct PermutationCheckBus {
    pub index: BusIndex,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum PermutationInteractionType {
    Send,
    Receive,
}

impl PermutationCheckBus {
    pub const fn new(index: BusIndex) -> Self {
        Self { index }
    }

    /// Send a message.
    ///
    /// Caller must constrain `enabled` to be boolean.
    pub fn send<AB, E>(
        &self,
        builder: &mut AB,
        message: impl IntoIterator<Item = E>,
        enabled: impl Into<AB::Expr>,
    ) where
        AB: InteractionBuilder,
        E: Into<AB::Expr>,
    {
        // We embed the multiplicity `enabled` as an integer {0, 1}.
        builder.push_interaction(self.index, message, enabled, 1);
    }

    /// Receive a message.
    ///
    /// Caller must constrain `enabled` to be boolean.
    pub fn receive<AB, E>(
        &self,
        builder: &mut AB,
        message: impl IntoIterator<Item = E>,
        enabled: impl Into<AB::Expr>,
    ) where
        AB: InteractionBuilder,
        E: Into<AB::Expr>,
    {
        // We embed the multiplicity `enabled` as an integer {0, -1}.
        builder.push_interaction(self.index, message, -enabled.into(), 1);
    }

    /// Send or receive determined by `interaction_type`.
    ///
    /// Caller must constrain `enabled` to be boolean.
    pub fn send_or_receive<AB, E>(
        &self,
        builder: &mut AB,
        interaction_type: PermutationInteractionType,
        message: impl IntoIterator<Item = E>,
        enabled: impl Into<AB::Expr>,
    ) where
        AB: InteractionBuilder,
        E: Into<AB::Expr>,
    {
        match interaction_type {
            PermutationInteractionType::Send => self.send(builder, message, enabled),
            PermutationInteractionType::Receive => self.receive(builder, message, enabled),
        }
    }

    /// Send or receive a message determined by the expression `direction`.
    ///
    /// Direction = 1 means send, direction = -1 means receive, and direction = 0 means disabled.
    ///
    /// Caller must constrain that direction is in {-1, 0, 1}.
    pub fn interact<AB, E>(
        &self,
        builder: &mut AB,
        message: impl IntoIterator<Item = E>,
        direction: impl Into<AB::Expr>,
    ) where
        AB: InteractionBuilder,
        E: Into<AB::Expr>,
    {
        // We embed the multiplicity `direction` as an integer {-1, 0, 1}.
        builder.push_interaction(self.index, message, direction.into(), 1);
    }
}

pub struct RapPhaseProverData<Challenge> {
    /// Challenges from the challenger in this phase that determine RAP constraints and exposed values.
    pub challenges: Vec<Challenge>,

    /// After challenge trace per air computed as a function of `challenges`.
    pub after_challenge_trace_per_air: Vec<Option<RowMajorMatrix<Challenge>>>,

    /// Public values of the phase that are functions of `challenges`.
    pub exposed_values_per_air: Vec<Option<Vec<Challenge>>>,
}

#[derive(Default)]
pub struct RapPhaseVerifierData<Challenge> {
    /// Challenges from the challenger in this phase that determine RAP constraints and exposed values.
    pub challenges_per_phase: Vec<Vec<Challenge>>,
}

#[derive(Debug)]
pub struct RapPhaseShape {
    pub num_challenges: usize,

    pub num_exposed_values: usize,

    /// Any additional rotations to open at in the permutation PCS round.
    ///
    /// Specifies that each `i` in `extra_opening_rots` should be opened at
    /// `zeta * g^i` (in addition to `zeta` and `zeta * g`).
    pub extra_opening_rots: Vec<usize>,
}

/// Supported challenge phases in a RAP.
#[derive(Debug, Copy, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[repr(u8)]
pub enum RapPhaseSeqKind {
    // GkrLogUp,
    /// Up to one phase with prover/verifier given by [[fri_log_up::FriLogUpPhase]] and
    /// constraints given by [[fri_log_up::eval_fri_log_up_phase]].
    FriLogUp,
}

impl RapPhaseSeqKind {
    pub fn shape(&self) -> Vec<RapPhaseShape> {
        match self {
            RapPhaseSeqKind::FriLogUp => vec![RapPhaseShape {
                num_challenges: STARK_LU_NUM_CHALLENGES,
                num_exposed_values: STARK_LU_NUM_EXPOSED_VALUES,
                extra_opening_rots: vec![],
            }],
        }
    }
}

/// Defines a particular protocol for the "after challenge" phase in a RAP.
///
/// A [RapPhaseSeq] is defined by the proving and verifying methods implemented in this trait,
/// as well as via some "eval" method that is determined by `RapPhaseId`.
pub trait RapPhaseSeq<F, Challenge, Challenger> {
    type PartialProof: Clone + Serialize + DeserializeOwned;
    /// Preprocessed data necessary for the RAP partial proving
    type PartialProvingKey: Clone + Serialize + DeserializeOwned;
    type Error: Debug;

    const ID: RapPhaseSeqKind;

    fn log_up_security_params(&self) -> &LogUpSecurityParameters;

    /// The protocol parameters for the challenge phases may depend on the AIR constraints.
    fn generate_pk_per_air(
        &self,
        symbolic_constraints_per_air: &[SymbolicConstraints<F>],
        max_constraint_degree: usize,
    ) -> Vec<Self::PartialProvingKey>;

    /// Partially prove the challenge phases,
    ///
    /// Samples challenges, generates after challenge traces and exposed values, and proves any
    /// extra-STARK part of the protocol.
    ///
    /// "Partial" refers to the fact that some STARK parts of the protocol---namely, the constraints
    /// on the after challenge traces returned in `RapPhaseProverData`---are handled external to
    /// this function.
    fn partially_prove(
        &self,
        challenger: &mut Challenger,
        constraints_per_air: &[&SymbolicConstraints<F>],
        params_per_air: &[&Self::PartialProvingKey],
        trace_view_per_air: Vec<PairTraceView<F>>,
    ) -> Option<(Self::PartialProof, RapPhaseProverData<Challenge>)>;

    /// Partially verifies the challenge phases.
    ///
    /// Assumes the shape of `exposed_values_per_air_per_phase` is verified externally.
    ///
    /// An implementation of this function must sample challenges for the challenge phases and then
    /// observe the exposed values and commitment.
    fn partially_verify<Commitment: Clone>(
        &self,
        challenger: &mut Challenger,
        partial_proof: Option<&Self::PartialProof>,
        exposed_values_per_air_per_phase: &[Vec<Vec<Challenge>>],
        commitments_per_phase: &[Commitment],
        // per commitment, per matrix, per rotation, per column
        after_challenge_opened_values: &[Vec<Vec<Vec<Challenge>>>],
    ) -> (RapPhaseVerifierData<Challenge>, Result<(), Self::Error>)
    where
        Challenger: CanObserve<Commitment>;
}

type PairTraceView<'a, F> = PairView<Arc<RowMajorMatrix<F>>, F>;

/// Parameters to ensure sufficient soundness of the LogUp part of the protocol.
#[derive(Clone, Debug, Serialize, Deserialize)]
#[repr(C)]
pub struct LogUpSecurityParameters {
    /// A bound on the total number of interactions.
    /// Determines a constraint at keygen that is checked by the verifier.
    pub max_interaction_count: u32,
    /// A bound on the base-2 logarithm of the length of the longest interaction. Checked in keygen.
    pub log_max_message_length: u32,
    /// The number of proof-of-work bits for the LogUp proof-of-work phase.
    pub log_up_pow_bits: usize,
}

impl LogUpSecurityParameters {
    /// The number of conjectured bits of security.
    pub fn conjectured_bits_of_security<F: Field>(&self) -> u32 {
        // See Section 4 of [docs/Soundness_of_Interactions_via_LogUp.pdf].
        let log_order = u32::try_from(F::order().bits() - 1).unwrap();
        log_order
            - log2_ceil_usize(2 * self.max_interaction_count as usize) as u32  // multiply by two to account for the poles as well
            - self.log_max_message_length
            + u32::try_from(self.log_up_pow_bits).unwrap()
    }
    pub fn max_message_length(&self) -> usize {
        2usize
            .checked_pow(self.log_max_message_length)
            .expect("max_message_length overflowed usize")
    }
}
