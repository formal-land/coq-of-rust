use {
    pinocchio::{account_info::AccountInfo, program_error::ProgramError, ProgramResult},
    spl_token_interface::{
        error::TokenError,
        state::{account::Account, load_unchecked, Initializable},
    },
};

#[inline(always)]
pub fn process_initialize_immutable_owner(accounts: &[AccountInfo]) -> ProgramResult {
    let token_account_info = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;

    // SAFETY: single immutable borrow to `token_account_info` account data.
    let account = unsafe { load_unchecked::<Account>(token_account_info.borrow_data_unchecked())? };

    if account.is_initialized()? {
        return Err(TokenError::AlreadyInUse.into());
    }
    // Please upgrade to SPL Token 2022 for immutable owner support.
    Ok(())
}
