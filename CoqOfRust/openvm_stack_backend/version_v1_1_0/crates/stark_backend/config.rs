//! [StarkGenericConfig](config::StarkGenericConfig) and associated types. Originally taken from Plonky3 under MIT license.

use std::marker::PhantomData;

use p3_challenger::{CanObserve, CanSample, FieldChallenger};
use p3_commit::{Pcs, PolynomialSpace};
use p3_field::{ExtensionField, Field};

use crate::interaction::RapPhaseSeq;

/// Based on [p3_uni_stark::StarkGenericConfig].
pub trait StarkGenericConfig
where
    Domain<Self>: Send + Sync,
    Com<Self>: Send + Sync,
    PcsProof<Self>: Send + Sync,
    PcsProverData<Self>: Send + Sync,
    RapPhaseSeqPartialProof<Self>: Send + Sync,
    RapPartialProvingKey<Self>: Send + Sync,
{
    /// The PCS used to commit to trace polynomials.
    type Pcs: Pcs<Self::Challenge, Self::Challenger>;

    /// The RAP challenge phases used to establish, e.g., that interactions are balanced.
    type RapPhaseSeq: RapPhaseSeq<Val<Self>, Self::Challenge, Self::Challenger>;

    /// The field from which most random challenges are drawn.
    type Challenge: ExtensionField<Val<Self>> + Send + Sync;

    /// The challenger (Fiat-Shamir) implementation used.
    type Challenger: FieldChallenger<Val<Self>>
        + CanObserve<<Self::Pcs as Pcs<Self::Challenge, Self::Challenger>>::Commitment>
        + CanSample<Self::Challenge>;

    fn pcs(&self) -> &Self::Pcs;

    fn rap_phase_seq(&self) -> &Self::RapPhaseSeq;
}

pub type Val<SC> = <<<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Domain as PolynomialSpace>::Val;

pub type Com<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Commitment;

pub type PcsProverData<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::ProverData;

pub type PcsProof<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Proof;

pub type PcsError<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Error;

pub type Domain<SC> = <<SC as StarkGenericConfig>::Pcs as Pcs<
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Domain;

pub type RapPhaseSeqPartialProof<SC> = <<SC as StarkGenericConfig>::RapPhaseSeq as RapPhaseSeq<
    Val<SC>,
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::PartialProof;

pub type RapPartialProvingKey<SC> = <<SC as StarkGenericConfig>::RapPhaseSeq as RapPhaseSeq<
    Val<SC>,
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::PartialProvingKey;

pub type RapPhaseSeqError<SC> = <<SC as StarkGenericConfig>::RapPhaseSeq as RapPhaseSeq<
    Val<SC>,
    <SC as StarkGenericConfig>::Challenge,
    <SC as StarkGenericConfig>::Challenger,
>>::Error;

pub type PackedVal<SC> = <Val<SC> as Field>::Packing;

pub type PackedChallenge<SC> =
    <<SC as StarkGenericConfig>::Challenge as ExtensionField<Val<SC>>>::ExtensionPacking;

#[derive(Debug)]
pub struct StarkConfig<Pcs, RapPhaseSeq, Challenge, Challenger> {
    pcs: Pcs,
    rap_phase: RapPhaseSeq,
    _phantom: PhantomData<(Challenge, Challenger)>,
}

impl<Pcs, RapPhaseSeq, Challenge, Challenger> StarkConfig<Pcs, RapPhaseSeq, Challenge, Challenger> {
    pub const fn new(pcs: Pcs, rap_phase: RapPhaseSeq) -> Self {
        Self {
            pcs,
            rap_phase,
            _phantom: PhantomData,
        }
    }
}

impl<Pcs, Rps, Challenge, Challenger> StarkGenericConfig
    for StarkConfig<Pcs, Rps, Challenge, Challenger>
where
    Challenge: ExtensionField<<Pcs::Domain as PolynomialSpace>::Val>,
    Pcs: p3_commit::Pcs<Challenge, Challenger>,
    Pcs::Domain: Send + Sync,
    Pcs::Commitment: Send + Sync,
    Pcs::ProverData: Send + Sync,
    Pcs::Proof: Send + Sync,
    Rps: RapPhaseSeq<<Pcs::Domain as PolynomialSpace>::Val, Challenge, Challenger>,
    Rps::PartialProof: Send + Sync,
    Rps::PartialProvingKey: Send + Sync,
    Challenger: FieldChallenger<<Pcs::Domain as PolynomialSpace>::Val>
        + CanObserve<<Pcs as p3_commit::Pcs<Challenge, Challenger>>::Commitment>
        + CanSample<Challenge>,
{
    type Pcs = Pcs;
    type RapPhaseSeq = Rps;
    type Challenge = Challenge;
    type Challenger = Challenger;

    fn pcs(&self) -> &Self::Pcs {
        &self.pcs
    }
    fn rap_phase_seq(&self) -> &Self::RapPhaseSeq {
        &self.rap_phase
    }
}

pub struct UniStarkConfig<SC>(pub SC);

impl<SC: StarkGenericConfig> p3_uni_stark::StarkGenericConfig for UniStarkConfig<SC> {
    type Pcs = SC::Pcs;

    type Challenge = SC::Challenge;

    type Challenger = SC::Challenger;

    fn pcs(&self) -> &Self::Pcs {
        self.0.pcs()
    }
}
