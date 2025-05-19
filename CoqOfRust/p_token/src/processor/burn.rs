use {
    super::{shared, unpack_amount},
    pinocchio::{account_info::AccountInfo, ProgramResult},
};

#[inline(always)]
pub fn process_burn(accounts: &[AccountInfo], instruction_data: &[u8]) -> ProgramResult {
    let amount = unpack_amount(instruction_data)?;

    shared::burn::process_burn(accounts, amount, None)
}
