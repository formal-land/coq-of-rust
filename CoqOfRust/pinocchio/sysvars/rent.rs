//! This account contains the current cluster rent.
//!
//! This is required for the rent sysvar implementation.

use super::Sysvar;
use crate::{
    account_info::{AccountInfo, Ref},
    impl_sysvar_get,
    program_error::ProgramError,
    pubkey::Pubkey,
};

/// The ID of the rent sysvar.
pub const RENT_ID: Pubkey = [
    6, 167, 213, 23, 25, 44, 92, 81, 33, 140, 201, 76, 61, 74, 241, 127, 88, 218, 238, 8, 155, 161,
    253, 68, 227, 219, 217, 138, 0, 0, 0, 0,
];

/// Default rental rate in lamports/byte-year.
///
/// This calculation is based on:
/// - 10^9 lamports per SOL
/// - $1 per SOL
/// - $0.01 per megabyte day
/// - $3.65 per megabyte year
pub const DEFAULT_LAMPORTS_PER_BYTE_YEAR: u64 = 1_000_000_000 / 100 * 365 / (1024 * 1024);

/// Default amount of time (in years) the balance has to include rent for the
/// account to be rent exempt.
pub const DEFAULT_EXEMPTION_THRESHOLD: f64 = 2.0;

/// Default amount of time (in years) the balance has to include rent for the
/// account to be rent exempt as a `u64`.
const DEFAULT_EXEMPTION_THRESHOLD_AS_U64: u64 = 2;

/// The `u64` representation of the default exemption threshold.
///
/// This is used to check whether the `f64` value can be safely cast to a `u64`.
const F64_EXEMPTION_THRESHOLD_AS_U64: u64 = 4611686018427387904;

/// Default percentage of collected rent that is burned.
///
/// Valid values are in the range [0, 100]. The remaining percentage is
/// distributed to validators.
pub const DEFAULT_BURN_PERCENT: u8 = 50;

/// Account storage overhead for calculation of base rent.
///
/// This is the number of bytes required to store an account with no data. It is
/// added to an accounts data length when calculating [`Rent::minimum_balance`].
pub const ACCOUNT_STORAGE_OVERHEAD: u64 = 128;

/// Rent sysvar data
#[repr(C)]
#[derive(Clone, Debug, Default)]
pub struct Rent {
    /// Rental rate in lamports per byte-year
    pub lamports_per_byte_year: u64,

    /// Exemption threshold in years
    pub exemption_threshold: f64,

    /// Burn percentage
    pub burn_percent: u8,
}

impl Rent {
    /// The length of the `Rent` sysvar account data.
    pub const LEN: usize = 8 + 8 + 1;

    /// Return a `Rent` from the given account info.
    ///
    /// This method performs a check on the account info key.
    #[inline]
    pub fn from_account_info(account_info: &AccountInfo) -> Result<Ref<Rent>, ProgramError> {
        if account_info.key() != &RENT_ID {
            return Err(ProgramError::InvalidArgument);
        }
        Ok(Ref::map(account_info.try_borrow_data()?, |data| unsafe {
            Self::from_bytes_unchecked(data)
        }))
    }

    /// Return a `Rent` from the given account info.
    ///
    /// This method performs a check on the account info key, but does not
    /// perform the borrow check.
    ///
    /// # Safety
    ///
    /// The caller must ensure that it is safe to borrow the account data – e.g., there are
    /// no mutable borrows of the account data.
    #[inline]
    pub unsafe fn from_account_info_unchecked(
        account_info: &AccountInfo,
    ) -> Result<&Self, ProgramError> {
        if account_info.key() != &RENT_ID {
            return Err(ProgramError::InvalidArgument);
        }
        Ok(Self::from_bytes_unchecked(
            account_info.borrow_data_unchecked(),
        ))
    }

    /// Return a `Rent` from the given bytes.
    ///
    /// This method performs a length validation. The caller must ensure that `bytes` contains
    /// a valid representation of `Rent`.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<&Self, ProgramError> {
        if bytes.len() < Self::LEN {
            return Err(ProgramError::InvalidArgument);
        }
        // SAFETY: `bytes` has been validated to be at least `Self::LEN` bytes long; the
        // caller must ensure that `bytes` contains a valid representation of `Rent`.
        Ok(unsafe { Self::from_bytes_unchecked(bytes) })
    }

    /// Return a `Rent` from the given bytes.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `bytes` contains a valid representation of `Rent` and
    /// that is has the expected length.
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        &*(bytes.as_ptr() as *const Rent)
    }

    /// Calculate how much rent to burn from the collected rent.
    ///
    /// The first value returned is the amount burned. The second is the amount
    /// to distribute to validators.
    #[inline]
    pub fn calculate_burn(&self, rent_collected: u64) -> (u64, u64) {
        let burned_portion = (rent_collected * u64::from(self.burn_percent)) / 100;
        (burned_portion, rent_collected - burned_portion)
    }

    /// Rent due on account's data length with balance.
    #[inline]
    pub fn due(&self, balance: u64, data_len: usize, years_elapsed: f64) -> RentDue {
        if self.is_exempt(balance, data_len) {
            RentDue::Exempt
        } else {
            RentDue::Paying(self.due_amount(data_len, years_elapsed))
        }
    }

    /// Rent due for account that is known to be not exempt.
    #[inline]
    pub fn due_amount(&self, data_len: usize, years_elapsed: f64) -> u64 {
        let actual_data_len = data_len as u64 + ACCOUNT_STORAGE_OVERHEAD;
        let lamports_per_year = self.lamports_per_byte_year * actual_data_len;
        (lamports_per_year as f64 * years_elapsed) as u64
    }

    /// Calculates the minimum balance for rent exemption.
    ///
    /// This method avoids floating-point operations when the `exemption_threshold`
    /// is the default value.
    ///
    /// # Arguments
    ///
    /// * `data_len` - The number of bytes in the account
    ///
    /// # Returns
    ///
    /// The minimum balance in lamports for rent exemption.
    #[inline]
    pub fn minimum_balance(&self, data_len: usize) -> u64 {
        let bytes = data_len as u64;

        if self.is_default_rent_threshold() {
            ((ACCOUNT_STORAGE_OVERHEAD + bytes) * self.lamports_per_byte_year)
                * DEFAULT_EXEMPTION_THRESHOLD_AS_U64
        } else {
            (((ACCOUNT_STORAGE_OVERHEAD + bytes) * self.lamports_per_byte_year) as f64
                * self.exemption_threshold) as u64
        }
    }

    /// Determines if an account can be considered rent exempt.
    ///
    /// # Arguments
    ///
    /// * `lamports` - The balance of the account in lamports
    /// * `data_len` - The size of the account in bytes
    ///
    /// # Returns
    ///
    /// `true`` if the account is rent exempt, `false`` otherwise.
    #[inline]
    pub fn is_exempt(&self, lamports: u64, data_len: usize) -> bool {
        lamports >= self.minimum_balance(data_len)
    }

    /// Determines if the `exemption_threshold` is the default value.
    ///
    /// This is used to check whether the `f64` value can be safely cast to a `u64`
    /// to avoid floating-point operations.
    #[inline]
    fn is_default_rent_threshold(&self) -> bool {
        u64::from_le_bytes(self.exemption_threshold.to_le_bytes()) == F64_EXEMPTION_THRESHOLD_AS_U64
    }
}

impl Sysvar for Rent {
    impl_sysvar_get!(sol_get_rent_sysvar);
}

/// The return value of [`Rent::due`].
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum RentDue {
    /// Used to indicate the account is rent exempt.
    Exempt,
    /// The account owes this much rent.
    Paying(u64),
}

impl RentDue {
    /// Return the lamports due for rent.
    pub fn lamports(&self) -> u64 {
        match self {
            RentDue::Exempt => 0,
            RentDue::Paying(x) => *x,
        }
    }

    /// Return 'true' if rent exempt.
    pub fn is_exempt(&self) -> bool {
        match self {
            RentDue::Exempt => true,
            RentDue::Paying(_) => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::sysvars::rent::{
        ACCOUNT_STORAGE_OVERHEAD, DEFAULT_BURN_PERCENT, DEFAULT_EXEMPTION_THRESHOLD,
        DEFAULT_LAMPORTS_PER_BYTE_YEAR,
    };

    #[test]
    pub fn test_minimum_balance() {
        let mut rent = super::Rent {
            lamports_per_byte_year: DEFAULT_LAMPORTS_PER_BYTE_YEAR,
            exemption_threshold: DEFAULT_EXEMPTION_THRESHOLD,
            burn_percent: DEFAULT_BURN_PERCENT,
        };

        // Using the default exemption threshold.

        let balance = rent.minimum_balance(100);
        let calculated = (((ACCOUNT_STORAGE_OVERHEAD + 100) * rent.lamports_per_byte_year) as f64
            * rent.exemption_threshold) as u64;

        assert!(calculated > 0);
        assert_eq!(balance, calculated);

        // Using a different exemption threshold.
        rent.exemption_threshold = 0.5;

        let balance = rent.minimum_balance(100);
        let calculated = (((ACCOUNT_STORAGE_OVERHEAD + 100) * rent.lamports_per_byte_year) as f64
            * rent.exemption_threshold) as u64;

        assert!(calculated > 0);
        assert_eq!(balance, calculated);
    }
}
