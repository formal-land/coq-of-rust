use {
    core::{slice::from_raw_parts, str::from_utf8_unchecked},
    pinocchio::{
        account_info::AccountInfo, program_error::ProgramError, pubkey::Pubkey,
        syscalls::sol_memcpy_, ProgramResult,
    },
    spl_token_interface::{
        error::TokenError,
        program::ID as TOKEN_PROGRAM_ID,
        state::{
            load,
            multisig::{Multisig, MAX_SIGNERS},
            Transmutable,
        },
    },
};

pub mod amount_to_ui_amount;
pub mod approve;
pub mod approve_checked;
pub mod batch;
pub mod burn;
pub mod burn_checked;
pub mod close_account;
pub mod freeze_account;
pub mod get_account_data_size;
pub mod initialize_account;
pub mod initialize_account2;
pub mod initialize_account3;
pub mod initialize_immutable_owner;
pub mod initialize_mint;
pub mod initialize_mint2;
pub mod initialize_multisig;
pub mod initialize_multisig2;
pub mod mint_to;
pub mod mint_to_checked;
pub mod revoke;
pub mod set_authority;
pub mod sync_native;
pub mod thaw_account;
pub mod transfer;
pub mod transfer_checked;
pub mod ui_amount_to_amount;
pub mod withdraw_excess_lamports;
// Shared processors.
pub mod shared;

pub use {
    amount_to_ui_amount::process_amount_to_ui_amount, approve::process_approve,
    approve_checked::process_approve_checked, batch::process_batch, burn::process_burn,
    burn_checked::process_burn_checked, close_account::process_close_account,
    freeze_account::process_freeze_account, get_account_data_size::process_get_account_data_size,
    initialize_account::process_initialize_account,
    initialize_account2::process_initialize_account2,
    initialize_account3::process_initialize_account3,
    initialize_immutable_owner::process_initialize_immutable_owner,
    initialize_mint::process_initialize_mint, initialize_mint2::process_initialize_mint2,
    initialize_multisig::process_initialize_multisig,
    initialize_multisig2::process_initialize_multisig2, mint_to::process_mint_to,
    mint_to_checked::process_mint_to_checked, revoke::process_revoke,
    set_authority::process_set_authority, sync_native::process_sync_native,
    thaw_account::process_thaw_account, transfer::process_transfer,
    transfer_checked::process_transfer_checked, ui_amount_to_amount::process_ui_amount_to_amount,
    withdraw_excess_lamports::process_withdraw_excess_lamports,
};

/// Number of bytes in a `u64`.
const U64_BYTES: usize = core::mem::size_of::<u64>();

/// Maximum number of digits in a formatted `u64`.
///
/// The maximum number of digits is equal to the maximum number
/// of decimals (`u8::MAX`) plus the length of the decimal point
/// and the leading zero.
const MAX_FORMATTED_DIGITS: usize = u8::MAX as usize + 2;

/// Checks that the account is owned by the expected program.
#[inline(always)]
fn check_account_owner(account_info: &AccountInfo) -> ProgramResult {
    if account_info.is_owned_by(&TOKEN_PROGRAM_ID) {
        Ok(())
    } else {
        Err(ProgramError::IncorrectProgramId)
    }
}

/// Validates owner(s) are present.
///
/// Note that `owner_account_info` will be immutable borrowed when it represents
/// a multisig account, therefore it should not have any mutable borrows when
/// calling this function.
#[inline(always)]
#[allow(clippy::arithmetic_side_effects)]
fn validate_owner(
    expected_owner: &Pubkey,
    owner_account_info: &AccountInfo,
    signers: &[AccountInfo],
) -> ProgramResult {
    if expected_owner != owner_account_info.key() {
        return Err(TokenError::OwnerMismatch.into());
    }

    if owner_account_info.data_len() == Multisig::LEN
        && owner_account_info.is_owned_by(&TOKEN_PROGRAM_ID)
    {
        // SAFETY: the caller guarantees that there are no mutable borrows of
        // `owner_account_info` account data and the `load` validates that the
        // account is initialized; additionally, `Multisig` accounts are only
        // ever loaded in this function, which means that previous loads will
        // have already failed by the time we get here.
        let multisig = unsafe { load::<Multisig>(owner_account_info.borrow_data_unchecked())? };

        let mut num_signers = 0;
        let mut matched = [false; MAX_SIGNERS as usize];

        for signer in signers.iter() {
            for (position, key) in multisig.signers[0..multisig.n as usize].iter().enumerate() {
                if key == signer.key() && !matched[position] {
                    if !signer.is_signer() {
                        return Err(ProgramError::MissingRequiredSignature);
                    }
                    matched[position] = true;
                    num_signers += 1;
                }
            }
        }
        if num_signers < multisig.m {
            return Err(ProgramError::MissingRequiredSignature);
        }
    } else if !owner_account_info.is_signer() {
        return Err(ProgramError::MissingRequiredSignature);
    }

    Ok(())
}

/// Try to convert a UI representation of a token amount to its raw amount using
/// the given decimals field
#[allow(clippy::arithmetic_side_effects)]
fn try_ui_amount_into_amount(ui_amount: &str, decimals: u8) -> Result<u64, ProgramError> {
    let decimals = decimals as usize;
    let mut parts = ui_amount.split('.');

    // Splitting a string, even an empty one, will always yield an iterator of at
    // least length == 1.
    let amount_str = parts.next().unwrap();
    let after_decimal = parts.next().unwrap_or("");
    // Clean up trailing zeros.
    let after_decimal = after_decimal.trim_end_matches('0');

    // Validates the input.

    let length = amount_str.len();

    if (amount_str.is_empty() && after_decimal.is_empty())
        || parts.next().is_some()
        || after_decimal.len() > decimals
        || (length + decimals) > MAX_FORMATTED_DIGITS
    {
        return Err(ProgramError::InvalidArgument);
    }

    let mut digits = [b'0'; MAX_FORMATTED_DIGITS];

    // SAFETY: the total length of `amount_str` and `after_decimal` is less than
    // `MAX_FORMATTED_DIGITS`.
    unsafe {
        sol_memcpy_(digits.as_mut_ptr(), amount_str.as_ptr(), length as u64);

        sol_memcpy_(
            digits.as_mut_ptr().add(length),
            after_decimal.as_ptr(),
            after_decimal.len() as u64,
        );
    }

    let length = amount_str.len() + decimals;

    // SAFETY: `digits` only contains valid UTF-8 bytes.
    unsafe {
        from_utf8_unchecked(from_raw_parts(digits.as_ptr(), length))
            .parse::<u64>()
            .map_err(|_| ProgramError::InvalidArgument)
    }
}

/// Unpacks a `u64` amount from the instruction data.
#[inline(always)]
const fn unpack_amount(instruction_data: &[u8]) -> Result<u64, TokenError> {
    // expected u64 (8)
    if instruction_data.len() >= U64_BYTES {
        // SAFETY: The minimum size of the instruction data is `U64_BYTES` bytes.
        Ok(unsafe { u64::from_le_bytes(*(instruction_data.as_ptr() as *const [u8; U64_BYTES])) })
    } else {
        Err(TokenError::InvalidInstruction)
    }
}

/// Unpacks a `u64` amount and an optional `u8` from the instruction data.
#[inline(always)]
const fn unpack_amount_and_decimals(instruction_data: &[u8]) -> Result<(u64, u8), TokenError> {
    // expected u64 (8) + u8 (1)
    if instruction_data.len() >= 9 {
        let (amount, decimals) = instruction_data.split_at(U64_BYTES);
        Ok((
            // SAFETY: The size of `amount` is `U64_BYTES` bytes.
            unsafe { u64::from_le_bytes(*(amount.as_ptr() as *const [u8; U64_BYTES])) },
            decimals[0],
        ))
    } else {
        Err(TokenError::InvalidInstruction)
    }
}
