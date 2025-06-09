use {
    super::{shared, unpack_amount_and_decimals},
    pinocchio::{account_info::AccountInfo, ProgramResult},
};

#[inline(always)]
pub fn process_transfer_checked(
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let (amount, decimals) = unpack_amount_and_decimals(instruction_data)?;

    shared::transfer::process_transfer(accounts, amount, Some(decimals))
}
