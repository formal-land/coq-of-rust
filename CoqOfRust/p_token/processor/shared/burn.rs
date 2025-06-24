use {
    crate::processor::{check_account_owner, validate_owner},
    pinocchio::{account_info::AccountInfo, program_error::ProgramError, ProgramResult},
    spl_token_interface::{
        error::TokenError,
        state::{account::Account, load_mut, mint::Mint},
    },
};

#[inline(always)]
pub fn process_burn(
    accounts: &[AccountInfo],
    amount: u64,
    expected_decimals: Option<u8>,
) -> ProgramResult {
    let [source_account_info, mint_info, authority_info, remaining @ ..] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    // SAFETY: single mutable borrow to `source_account_info` account data and
    // `load_mut` validates that the account is initialized.
    let source_account =
        unsafe { load_mut::<Account>(source_account_info.borrow_mut_data_unchecked())? };
    // SAFETY: single mutable borrow to `mint_info` account data and
    // `load_mut` validates that the mint is initialized; additionally, an
    // account cannot be both a token account and a mint, so if duplicates are
    // passed in, one of them will fail the `load_mut` check.
    let mint = unsafe { load_mut::<Mint>(mint_info.borrow_mut_data_unchecked())? };

    if source_account.is_frozen()? {
        return Err(TokenError::AccountFrozen.into());
    }
    if source_account.is_native() {
        return Err(TokenError::NativeNotSupported.into());
    }

    // Ensure the source account has the sufficient amount. This is done before
    // the value is updated on the account.
    let updated_source_amount = source_account
        .amount()
        .checked_sub(amount)
        .ok_or(TokenError::InsufficientFunds)?;

    if mint_info.key() != &source_account.mint {
        return Err(TokenError::MintMismatch.into());
    }

    if let Some(expected_decimals) = expected_decimals {
        if expected_decimals != mint.decimals {
            return Err(TokenError::MintDecimalsMismatch.into());
        }
    }

    if !source_account.is_owned_by_system_program_or_incinerator() {
        match source_account.delegate() {
            Some(delegate) if authority_info.key() == delegate => {
                validate_owner(delegate, authority_info, remaining)?;

                let delegated_amount = source_account
                    .delegated_amount()
                    .checked_sub(amount)
                    .ok_or(TokenError::InsufficientFunds)?;
                source_account.set_delegated_amount(delegated_amount);

                if delegated_amount == 0 {
                    source_account.clear_delegate();
                }
            }
            _ => {
                validate_owner(&source_account.owner, authority_info, remaining)?;
            }
        }
    }

    // Updates the source account and mint supply.

    if amount == 0 {
        check_account_owner(source_account_info)?;
        check_account_owner(mint_info)?;
    } else {
        source_account.set_amount(updated_source_amount);
        // Note: The amount of a token account is always within the range of the
        // mint supply (`u64`).
        let mint_supply = mint.supply().checked_sub(amount).unwrap();
        mint.set_supply(mint_supply);
    }

    Ok(())
}
