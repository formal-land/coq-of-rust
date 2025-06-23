//! Information about the network's clock, ticks, slots, etc.

use super::Sysvar;
use crate::{
    account_info::{AccountInfo, Ref},
    impl_sysvar_get,
    program_error::ProgramError,
    pubkey::Pubkey,
};

/// The ID of the clock sysvar.
pub const CLOCK_ID: Pubkey = [
    6, 167, 213, 23, 24, 199, 116, 201, 40, 86, 99, 152, 105, 29, 94, 182, 139, 94, 184, 163, 155,
    75, 109, 92, 115, 85, 91, 33, 0, 0, 0, 0,
];

/// The unit of time given to a leader for encoding a block.
///
/// It is some some number of _ticks_ long.
pub type Slot = u64;

/// The unit of time a given leader schedule is honored.
///
/// It lasts for some number of [`Slot`]s.
pub type Epoch = u64;

/// An approximate measure of real-world time.
///
/// Expressed as Unix time (i.e. seconds since the Unix epoch).
pub type UnixTimestamp = i64;

/// A representation of network time.
///
/// All members of `Clock` start from 0 upon network boot.
#[repr(C)]
#[derive(Copy, Clone, Default)]
pub struct Clock {
    /// The current `Slot`.
    pub slot: Slot,

    /// The timestamp of the first `Slot` in this `Epoch`.
    pub epoch_start_timestamp: UnixTimestamp,

    /// The current `Epoch`.
    pub epoch: Epoch,

    /// The future `Epoch` for which the leader schedule has
    /// most recently been calculated.
    pub leader_schedule_epoch: Epoch,

    /// The approximate real world time of the current slot.
    ///
    /// This value was originally computed from genesis creation time and
    /// network time in slots, incurring a lot of drift. Following activation of
    /// the [`timestamp_correction` and `timestamp_bounding`][tsc] features it
    /// is calculated using a [validator timestamp oracle][oracle].
    ///
    /// [tsc]: https://docs.solanalabs.com/implemented-proposals/bank-timestamp-correction
    /// [oracle]: https://docs.solanalabs.com/implemented-proposals/validator-timestamp-oracle
    pub unix_timestamp: UnixTimestamp,
}

/// At 160 ticks/s, 64 ticks per slot implies that leader rotation and voting will happen
/// every 400 ms. A fast voting cadence ensures faster finality and convergence
pub const DEFAULT_TICKS_PER_SLOT: u64 = 64;

/// The default tick rate that the cluster attempts to achieve (160 per second).
///
/// Note that the actual tick rate at any given time should be expected to drift.
pub const DEFAULT_TICKS_PER_SECOND: u64 = 160;

/// The expected duration of a slot (400 milliseconds).
// Actually calculation is supposed to be derived DEFAULT_TICKS_PER_SLOT / DEFAULT_TICKS_PER_SECOND
pub const DEFAULT_MS_PER_SLOT: u64 = 1_000 * DEFAULT_TICKS_PER_SLOT / DEFAULT_TICKS_PER_SECOND;

impl Sysvar for Clock {
    impl_sysvar_get!(sol_get_clock_sysvar);
}

impl Clock {
    /// The length of the `Clock` sysvar account data.
    pub const LEN: usize = 8 + 8 + 8 + 8 + 8;

    /// Return a `Clock` from the given account info.
    ///
    /// This method performs a check on the account info key.
    #[inline]
    pub fn from_account_info(account_info: &AccountInfo) -> Result<Ref<Clock>, ProgramError> {
        if account_info.key() != &CLOCK_ID {
            return Err(ProgramError::InvalidArgument);
        }
        Ok(Ref::map(account_info.try_borrow_data()?, |data| unsafe {
            Self::from_bytes_unchecked(data)
        }))
    }

    /// Return a `Clock` from the given account info.
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
        if account_info.key() != &CLOCK_ID {
            return Err(ProgramError::InvalidArgument);
        }
        Ok(Self::from_bytes_unchecked(
            account_info.borrow_data_unchecked(),
        ))
    }

    /// Return a `Clock` from the given bytes.
    ///
    /// This method performs a length validation. The caller must ensure that `bytes` contains
    /// a valid representation of `Clock`.
    #[inline]
    pub fn from_bytes(bytes: &[u8]) -> Result<&Self, ProgramError> {
        if bytes.len() < Self::LEN {
            return Err(ProgramError::InvalidArgument);
        }
        // SAFETY: `bytes` has been validated to be at least `Self::LEN` bytes long; the
        // caller must ensure that `bytes` contains a valid representation of `Clock`.
        Ok(unsafe { Self::from_bytes_unchecked(bytes) })
    }

    /// Return a `Clock` from the given bytes.
    ///
    /// # Safety
    ///
    /// The caller must ensure that `bytes` contains a valid representation of `Clock` and
    /// that is has the expected length.
    #[inline]
    pub unsafe fn from_bytes_unchecked(bytes: &[u8]) -> &Self {
        &*(bytes.as_ptr() as *const Clock)
    }
}
