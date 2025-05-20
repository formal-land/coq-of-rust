use {
    crate::processor::{check_account_owner, validate_owner},
    pinocchio::{account_info::AccountInfo, program_error::ProgramError, ProgramResult},
    spl_token_interface::{
        error::TokenError,
        state::{account::Account, load, load_mut, load_mut_unchecked, mint::Mint},
    },
};

#[inline(always)]
#[allow(clippy::arithmetic_side_effects)]
pub fn process_transfer(
    accounts: &[AccountInfo],
    amount: u64,
    expected_decimals: Option<u8>,
) -> ProgramResult {
    // Accounts expected depend on whether we have the mint `decimals` or not; when
    // we have the mint `decimals`, we expect the mint account to be present.

    let (
        source_account_info,
        expected_mint_info,
        destination_account_info,
        authority_info,
        remaining,
    ) = if let Some(decimals) = expected_decimals {
        let [source_account_info, mint_info, destination_account_info, authority_info, remaining @ ..] =
            accounts
        else {
            return Err(ProgramError::NotEnoughAccountKeys);
        };
        (
            source_account_info,
            Some((mint_info, decimals)),
            destination_account_info,
            authority_info,
            remaining,
        )
    } else {
        let [source_account_info, destination_account_info, authority_info, remaining @ ..] =
            accounts
        else {
            return Err(ProgramError::NotEnoughAccountKeys);
        };
        (
            source_account_info,
            None,
            destination_account_info,
            authority_info,
            remaining,
        )
    };

    // Validates source and destination accounts.

    // SAFETY: single mutable borrow to `source_account_info` account data and
    // `load_mut` validates that the account is initialized.
    let source_account =
        unsafe { load_mut::<Account>(source_account_info.borrow_mut_data_unchecked())? };

    // Comparing whether the AccountInfo's "point" to the same account or
    // not - this is a faster comparison since it just checks the internal
    // raw pointer.
    let self_transfer = source_account_info == destination_account_info;

    // Implicitly validates that the account has enough tokens by calculating the
    // remaining amount - the amount is only updated on the account if the transfer
    // is successful.
    //
    // Note: the logic is partially duplicated for self transfers and transfers
    // to different accounts to improve CU consumption:
    //
    //   - self-transfer: we only need to check that the source account is not
    //     frozen and has enough tokens.
    //
    //   - transfers to different accounts: we need to check that the source and
    //     destination accounts are not frozen, have the same mint, and the source
    //     account has enough tokens.
    let remaining_amount = if self_transfer {
        if source_account.is_frozen()? {
            return Err(TokenError::AccountFrozen.into());
        }

        source_account
            .amount()
            .checked_sub(amount)
            .ok_or(TokenError::InsufficientFunds)?
    } else {
        // SAFETY: scoped immutable borrow to `destination_account_info` account data
        // and `load` validates that the account is initialized; additionally,
        // the account is guaranteed to be different than `source_account_info`.
        let destination_account =
            unsafe { load::<Account>(destination_account_info.borrow_data_unchecked())? };

        if source_account.is_frozen()? || destination_account.is_frozen()? {
            return Err(TokenError::AccountFrozen.into());
        }

        let remaining_amount = source_account
            .amount()
            .checked_sub(amount)
            .ok_or(TokenError::InsufficientFunds)?;

        if source_account.mint != destination_account.mint {
            return Err(TokenError::MintMismatch.into());
        }

        remaining_amount
    };

    // Validates the mint information.

    if let Some((mint_info, decimals)) = expected_mint_info {
        if mint_info.key() != &source_account.mint {
            return Err(TokenError::MintMismatch.into());
        }

        // SAFETY: single immutable borrow of `mint_info` account data and
        // `load` validates that the mint is initialized.
        let mint = unsafe { load::<Mint>(mint_info.borrow_data_unchecked())? };

        if decimals != mint.decimals {
            return Err(TokenError::MintDecimalsMismatch.into());
        }
    }

    // Validates the authority (delegate or owner).

    if source_account.delegate() == Some(authority_info.key()) {
        validate_owner(authority_info.key(), authority_info, remaining)?;

        let delegated_amount = source_account
            .delegated_amount()
            .checked_sub(amount)
            .ok_or(TokenError::InsufficientFunds)?;

        if !self_transfer {
            source_account.set_delegated_amount(delegated_amount);

            if delegated_amount == 0 {
                source_account.clear_delegate();
            }
        }
    } else {
        validate_owner(&source_account.owner, authority_info, remaining)?;
    }

    if self_transfer || amount == 0 {
        // Validates the token accounts owner since we are not writing
        // to these account.
        check_account_owner(source_account_info)?;
        check_account_owner(destination_account_info)?;
    } else {
        // Moves the tokens.

        source_account.set_amount(remaining_amount);

        // SAFETY: single mutable borrow to `destination_account_info` account data; the
        // account is guaranteed to be initialized and different than
        // `source_account_info`; it was also already validated to be a token
        // account.
        let destination_account = unsafe {
            load_mut_unchecked::<Account>(destination_account_info.borrow_mut_data_unchecked())?
        };
        // Note: The amount of a token account is always within the range of the
        // mint supply (`u64`).
        destination_account.set_amount(destination_account.amount() + amount);

        if source_account.is_native() {
            // SAFETY: single mutable borrow to `source_account_info` lamports.
            let source_lamports = unsafe { source_account_info.borrow_mut_lamports_unchecked() };
            *source_lamports = source_lamports
                .checked_sub(amount)
                .ok_or(TokenError::Overflow)?;

            // SAFETY: single mutable borrow to `destination_account_info` lamports; the
            // account is already validated to be different from
            // `source_account_info`.
            let destination_lamports =
                unsafe { destination_account_info.borrow_mut_lamports_unchecked() };
            *destination_lamports = destination_lamports
                .checked_add(amount)
                .ok_or(TokenError::Overflow)?;
        }
    }

    Ok(())
}
