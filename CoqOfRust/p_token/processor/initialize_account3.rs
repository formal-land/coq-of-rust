use {
    super::shared,
    pinocchio::{
        account_info::AccountInfo,
        pubkey::{Pubkey, PUBKEY_BYTES},
        ProgramResult,
    },
    spl_token_interface::error::TokenError,
};

#[inline(always)]
pub fn process_initialize_account3(
    accounts: &[AccountInfo],
    instruction_data: &[u8],
) -> ProgramResult {
    let owner = if instruction_data.len() >= PUBKEY_BYTES {
        // SAFETY: The minimum size of the instruction data is `PUBKEY_BYTES` bytes.
        unsafe { &*(instruction_data.as_ptr() as *const Pubkey) }
    } else {
        return Err(TokenError::InvalidInstruction.into());
    };

    shared::initialize_account::process_initialize_account(accounts, Some(owner), false)
}
