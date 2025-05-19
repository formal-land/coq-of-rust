use {
    crate::processor::{check_account_owner, validate_owner},
    pinocchio::{account_info::AccountInfo, program_error::ProgramError, ProgramResult},
    spl_token_interface::{
        error::TokenError,
        state::{account::Account, load_mut, mint::Mint},
    },
};

#[inline(always)]
#[allow(clippy::arithmetic_side_effects)]
pub fn process_mint_to(
    accounts: &[AccountInfo],
    amount: u64,
    expected_decimals: Option<u8>,
) -> ProgramResult {
    let [mint_info, destination_account_info, owner_info, remaining @ ..] = accounts else {
        return Err(ProgramError::NotEnoughAccountKeys);
    };

    // Validates the destination account.

    // SAFETY: single mutable borrow to `destination_account_info` account data and
    // `load_mut` validates that the account is initialized.
    let destination_account =
        unsafe { load_mut::<Account>(destination_account_info.borrow_mut_data_unchecked())? };

    if destination_account.is_frozen()? {
        return Err(TokenError::AccountFrozen.into());
    }

    if destination_account.is_native() {
        return Err(TokenError::NativeNotSupported.into());
    }

    if mint_info.key() != &destination_account.mint {
        return Err(TokenError::MintMismatch.into());
    }

    // SAFETY: single mutable borrow to `mint_info` account data and
    // `load_mut` validates that the mint is initialized.
    let mint = unsafe { load_mut::<Mint>(mint_info.borrow_mut_data_unchecked())? };

    if let Some(expected_decimals) = expected_decimals {
        if expected_decimals != mint.decimals {
            return Err(TokenError::MintDecimalsMismatch.into());
        }
    }

    match mint.mint_authority() {
        Some(mint_authority) => validate_owner(mint_authority, owner_info, remaining)?,
        None => return Err(TokenError::FixedSupply.into()),
    }

    if amount == 0 {
        // Validates the accounts' owner since we are not writing
        // to these account.
        check_account_owner(mint_info)?;
        check_account_owner(destination_account_info)?;
    } else {
        let mint_supply = mint
            .supply()
            .checked_add(amount)
            .ok_or(TokenError::Overflow)?;
        mint.set_supply(mint_supply);

        // This should not fail since there is no overflow on the mint supply.
        destination_account.set_amount(destination_account.amount() + amount);
    }

    Ok(())
}
