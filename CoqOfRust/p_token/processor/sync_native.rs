use {
    super::check_account_owner,
    pinocchio::{account_info::AccountInfo, program_error::ProgramError, ProgramResult},
    spl_token_interface::{
        error::TokenError,
        state::{account::Account, load_mut},
    },
};

#[inline(always)]
pub fn process_sync_native(accounts: &[AccountInfo]) -> ProgramResult {
    let native_account_info = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;

    check_account_owner(native_account_info)?;

    // SAFETY: single mutable borrow to `native_account_info` account data and
    // `load_mut` validates that the account is initialized.
    let native_account =
        unsafe { load_mut::<Account>(native_account_info.borrow_mut_data_unchecked())? };

    if let Option::Some(rent_exempt_reserve) = native_account.native_amount() {
        let new_amount = native_account_info
            .lamports()
            .checked_sub(rent_exempt_reserve)
            .ok_or(TokenError::Overflow)?;

        if new_amount < native_account.amount() {
            return Err(TokenError::InvalidState.into());
        }
        native_account.set_amount(new_amount);
    } else {
        return Err(TokenError::NonNativeNotSupported.into());
    }

    Ok(())
}
