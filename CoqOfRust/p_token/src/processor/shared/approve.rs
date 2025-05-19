use {
    crate::processor::validate_owner,
    pinocchio::{account_info::AccountInfo, program_error::ProgramError, ProgramResult},
    spl_token_interface::{
        error::TokenError,
        state::{account::Account, load, load_mut, mint::Mint},
    },
};

#[inline(always)]
pub fn process_approve(
    accounts: &[AccountInfo],
    amount: u64,
    expected_decimals: Option<u8>,
) -> ProgramResult {
    // Accounts expected depend on whether we have the mint `decimals` or not; when
    // we have the mint `decimals`, we expect the mint account to be present.

    let (source_account_info, expected_mint_info, delegate_info, owner_info, remaining) =
        if let Some(expected_decimals) = expected_decimals {
            let [source_account_info, expected_mint_info, delegate_info, owner_info, remaining @ ..] =
                accounts
            else {
                return Err(ProgramError::NotEnoughAccountKeys);
            };

            (
                source_account_info,
                Some((expected_mint_info, expected_decimals)),
                delegate_info,
                owner_info,
                remaining,
            )
        } else {
            let [source_account_info, delegate_info, owner_info, remaining @ ..] = accounts else {
                return Err(ProgramError::NotEnoughAccountKeys);
            };
            (
                source_account_info,
                None,
                delegate_info,
                owner_info,
                remaining,
            )
        };

    // Validates source account.

    // SAFETY: single mutable borrow to `source_account_info` account data and
    // `load_mut` validates that the account is initialized.
    let source_account =
        unsafe { load_mut::<Account>(source_account_info.borrow_mut_data_unchecked())? };

    if source_account.is_frozen()? {
        return Err(TokenError::AccountFrozen.into());
    }

    if let Some((mint_info, expected_decimals)) = expected_mint_info {
        if mint_info.key() != &source_account.mint {
            return Err(TokenError::MintMismatch.into());
        }

        // SAFETY: single immutable borrow of `mint_info` account data and
        // `load` validates that the mint is initialized.
        let mint = unsafe { load::<Mint>(mint_info.borrow_data_unchecked())? };

        if expected_decimals != mint.decimals {
            return Err(TokenError::MintDecimalsMismatch.into());
        }
    }

    validate_owner(&source_account.owner, owner_info, remaining)?;

    // Sets the delegate and delegated amount.

    source_account.set_delegate(delegate_info.key());
    source_account.set_delegated_amount(amount);

    Ok(())
}
