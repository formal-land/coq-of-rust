use {
    super::{shared, unpack_amount_and_decimals},
    pinocchio::{account_info::AccountInfo, ProgramResult},
};

#[inline(always)]
pub fn process_approve_checked(accounts: &[AccountInfo], instruction_data: &[u8]) -> ProgramResult {
    let (amount, decimals) = unpack_amount_and_decimals(instruction_data)?;

    shared::approve::process_approve(accounts, amount, Some(decimals))
}
