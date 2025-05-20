use {
    super::{shared, unpack_amount_and_decimals},
    pinocchio::{account_info::AccountInfo, ProgramResult},
};

#[inline(always)]
pub fn process_mint_to_checked(accounts: &[AccountInfo], instruction_data: &[u8]) -> ProgramResult {
    let (amount, decimals) = unpack_amount_and_decimals(instruction_data)?;

    shared::mint_to::process_mint_to(accounts, amount, Some(decimals))
}
