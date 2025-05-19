use {
    super::validate_owner,
    pinocchio::{account_info::AccountInfo, program_error::ProgramError, ProgramResult},
    spl_token_interface::{
        error::TokenError,
        state::{
            account::{Account, INCINERATOR_ID},
            load,
        },
    },
};

#[inline(always)]
pub fn process_close_account(accounts: &[AccountInfo]) -> ProgramResult {
    let [source_account_info, destination_account_info, authority_info, remaining @ ..] = accounts
    else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    // Comparing whether the AccountInfo's "point" to the same account or
    // not - this is a faster comparison since it just checks the internal
    // raw pointer.
    if source_account_info == destination_account_info {
        return Err(ProgramError::InvalidAccountData);
    } else {
        // SAFETY: scoped immutable borrow to `source_account_info` account data and
        // `load` validates that the account is initialized.
        let source_account =
            unsafe { load::<Account>(source_account_info.borrow_data_unchecked())? };

        if !source_account.is_native() && source_account.amount() != 0 {
            return Err(TokenError::NonNativeHasBalance.into());
        }

        let authority = source_account
            .close_authority()
            .unwrap_or(&source_account.owner);

        if !source_account.is_owned_by_system_program_or_incinerator() {
            validate_owner(authority, authority_info, remaining)?;
        } else if destination_account_info.key() != &INCINERATOR_ID {
            return Err(ProgramError::InvalidAccountData);
        }
    }

    let destination_starting_lamports = destination_account_info.lamports();
    // SAFETY: single mutable borrow to `destination_account_info` lamports and
    // there are no "active" borrows of `source_account_info` account data.
    unsafe {
        // Moves the lamports to the destination account.
        *destination_account_info.borrow_mut_lamports_unchecked() = destination_starting_lamports
            .checked_add(source_account_info.lamports())
            .ok_or(TokenError::Overflow)?;
        // Closes the source account.
        source_account_info.close_unchecked();
    }

    Ok(())
}
