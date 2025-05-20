use {
    super::{check_account_owner, try_ui_amount_into_amount},
    core::str::from_utf8,
    pinocchio::{
        account_info::AccountInfo, program::set_return_data, program_error::ProgramError,
        ProgramResult,
    },
    spl_token_interface::{
        error::TokenError,
        state::{load, mint::Mint},
    },
};

pub fn process_ui_amount_to_amount(
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let ui_amount = from_utf8(instruction_data).map_err(|_error| TokenError::InvalidInstruction)?;

    let mint_info = accounts.first().ok_or(ProgramError::NotEnoughAccountKeys)?;
    check_account_owner(mint_info)?;
    // SAFETY: single immutable borrow to `mint_info` account data and
    // `load` validates that the mint is initialized.
    let mint = unsafe {
        load::<Mint>(mint_info.borrow_data_unchecked()).map_err(|_| TokenError::InvalidMint)?
    };

    let amount = try_ui_amount_into_amount(ui_amount, mint.decimals)?;
    set_return_data(&amount.to_le_bytes());

    Ok(())
}
