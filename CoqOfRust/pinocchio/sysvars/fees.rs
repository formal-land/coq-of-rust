//! Calculation of transaction fees.

use super::{clock::DEFAULT_MS_PER_SLOT, Sysvar};
use crate::impl_sysvar_get;

/// Fee calculator for processing transactions
#[derive(Debug, Default, Clone, Copy)]
pub struct FeeCalculator {
    /// The current cost of a signature in lamports.
    /// This amount may increase/decrease over time based on cluster processing
    /// load.
    pub lamports_per_signature: u64,
}

impl FeeCalculator {
    /// Create a new instance of the FeeCalculator
    pub fn new(lamports_per_signature: u64) -> Self {
        Self {
            lamports_per_signature,
        }
    }
}

/// Governs the fee rate for the cluster
#[derive(Debug, Clone)]
pub struct FeeRateGovernor {
    /// The current cost of a signature
    pub lamports_per_signature: u64,
    /// The target cost of a signature
    pub target_lamports_per_signature: u64,
    /// The target number of signatures per slot
    pub target_signatures_per_slot: u64,
    /// Minimum lamports per signature
    pub min_lamports_per_signature: u64,
    /// Maximum lamports per signature
    pub max_lamports_per_signature: u64,
    /// Percentage of fees to burn (0-100)
    pub burn_percent: u8,
}

/// Default lamports per signature.
pub const DEFAULT_TARGET_LAMPORTS_PER_SIGNATURE: u64 = 10_000;

/// Default signatures per slot.
pub const DEFAULT_TARGET_SIGNATURES_PER_SLOT: u64 = 50 * DEFAULT_MS_PER_SLOT;

/// Default percentage of fees to burn.
pub const DEFAULT_BURN_PERCENT: u8 = 50;

impl Default for FeeRateGovernor {
    fn default() -> Self {
        Self {
            lamports_per_signature: 0,
            target_lamports_per_signature: DEFAULT_TARGET_LAMPORTS_PER_SIGNATURE, // Example default value
            target_signatures_per_slot: DEFAULT_TARGET_SIGNATURES_PER_SLOT, // Assuming 400ms per slot
            min_lamports_per_signature: 0,
            max_lamports_per_signature: 0,
            burn_percent: DEFAULT_BURN_PERCENT,
        }
    }
}

impl FeeRateGovernor {
    /// Create a new FeeCalculator based on current cluster signature throughput
    pub fn create_fee_calculator(&self) -> FeeCalculator {
        FeeCalculator::new(self.lamports_per_signature)
    }

    /// Calculate unburned fee from a fee total, returns (unburned, burned)
    pub fn burn(&self, fees: u64) -> (u64, u64) {
        let burned = fees * u64::from(self.burn_percent) / 100;
        (fees - burned, burned)
    }
}

/// Fees sysvar
#[derive(Debug, Default)]
pub struct Fees {
    /// Fee calculator for processing transactions
    pub fee_calculator: FeeCalculator,
    /// Fee rate governor
    pub fee_rate_governor: FeeRateGovernor,
}

impl Fees {
    /// Create a new instance of the Fees sysvar
    pub fn new(fee_calculator: FeeCalculator, fee_rate_governor: FeeRateGovernor) -> Self {
        Self {
            fee_calculator,
            fee_rate_governor,
        }
    }
}

impl Sysvar for Fees {
    impl_sysvar_get!(sol_get_fees_sysvar);
}
