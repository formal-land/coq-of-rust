use {
    super::{check_account_owner, unpack_amount, MAX_FORMATTED_DIGITS},
    core::str::from_utf8_unchecked,
    pinocchio::{
        account_info::AccountInfo, program::set_return_data, program_error::ProgramError,
        ProgramResult,
    },
    pinocchio_log::logger::{Argument, Logger},
    spl_token_interface::{
        error::TokenError,
        state::{load, mint::Mint},
    },
};

pub fn process_amount_to_ui_amount(
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let amount = unpack_amount(instruction_data)?;

    let mint_info = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    check_account_owner(mint_info)?;
    // SAFETY: single immutable borrow to `mint_info` account data and
    // `load` validates that the mint is initialized.
    let mint = unsafe {
        load::<Mint>(mint_info.borrow_data_unchecked()).map_err(|_| TokenError::InvalidMint)?
    };

    let mut logger = Logger::<MAX_FORMATTED_DIGITS>::default();
    logger.append_with_args(amount, &[Argument::Precision(mint.decimals)]);
    // "Extract" the formatted string from the logger.
    //
    // SAFETY: the logger is guaranteed to be a valid UTF-8 string.
    let mut s = unsafe { from_utf8_unchecked(&logger) };

    if mint.decimals > 0 && s.contains('.') {
        let zeros_trimmed = s.trim_end_matches('0');
        s = zeros_trimmed.trim_end_matches('.');
    }

    set_return_data(s.as_bytes());

    Ok(())
}
