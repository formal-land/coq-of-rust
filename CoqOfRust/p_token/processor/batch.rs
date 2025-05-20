use {
    crate::entrypoint::inner_process_instruction,
    pinocchio::{account_info::AccountInfo, program_error::ProgramError, ProgramResult},
    spl_token_interface::error::TokenError,
};

/// The size of the batch instruction header.
///
/// The header of each instruction consists of two `u8` values:
///  * number of the accounts
///  * length of the instruction data
const IX_HEADER_SIZE: usize = 2;

#[allow(clippy::arithmetic_side_effects)]
pub fn process_batch(mut accounts: &[AccountInfo], mut instruction_data: &[u8]) -> ProgramResult {
    loop {
        // Validates the instruction data and accounts offset.

        if instruction_data.len() < IX_HEADER_SIZE {
            // The instruction data must have at least two bytes.
            return Err(TokenError::InvalidInstruction.into());
        }

        // SAFETY: The instruction data is guaranteed to have at least two bytes
        // (header) + one byte (discriminator) and the values are within the bounds
        // of an `usize`.
        let expected_accounts = unsafe { *instruction_data.get_unchecked(0) as usize };
        let data_offset = IX_HEADER_SIZE + unsafe { *instruction_data.get_unchecked(1) as usize };

        if instruction_data.len() < data_offset || data_offset == IX_HEADER_SIZE {
            return Err(TokenError::InvalidInstruction.into());
        }

        if accounts.len() < expected_accounts {
            return Err(ProgramError::NotEnoughAccountKeys);
        }

        // Process the instruction.

        // SAFETY: The instruction data and accounts lengths are already validated so
        // all slices are guaranteed to be valid.
        let (ix_accounts, ix_data) = unsafe {
            (
                accounts.get_unchecked(..expected_accounts),
                instruction_data.get_unchecked(IX_HEADER_SIZE..data_offset),
            )
        };

        inner_process_instruction(ix_accounts, ix_data)?;

        if data_offset == instruction_data.len() {
            // The batch is complete.
            break;
        }

        accounts = &accounts[expected_accounts..];
        instruction_data = &instruction_data[data_offset..];
    }

    Ok(())
}
