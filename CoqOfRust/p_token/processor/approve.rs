use {
    super::{shared, unpack_amount},
    pinocchio::{account_info::AccountInfo, ProgramResult},
};

#[inline(always)]
pub fn process_approve(accounts: &[AccountInfo], instruction_data: &[u8]) -> ProgramResult {
    let amount = unpack_amount(instruction_data)?;

    shared::approve::process_approve(accounts, amount, None)
}
