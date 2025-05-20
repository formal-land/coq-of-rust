use {
    super::shared,
    pinocchio::{account_info::AccountInfo, ProgramResult},
};

#[inline(always)]
pub fn process_initialize_mint(accounts: &[AccountInfo], instruction_data: &[u8]) -> ProgramResult {
    shared::initialize_mint::process_initialize_mint(accounts, instruction_data, true)
}
