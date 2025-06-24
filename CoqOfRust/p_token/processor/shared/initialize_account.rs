use {
    crate::processor::check_account_owner,
    pinocchio::{
        account_info::AccountInfo,
        program_error::ProgramError,
        pubkey::Pubkey,
        sysvars::{rent::Rent, Sysvar},
        ProgramResult,
    },
    spl_token_interface::{
        error::TokenError,
        native_mint::is_native_mint,
        state::{
            account::Account, account_state::AccountState, load, load_mut_unchecked, mint::Mint,
            Initializable,
        },
    },
};

#[inline(always)]
#[allow(clippy::arithmetic_side_effects)]
pub fn process_initialize_account(
    accounts: &[AccountInfo],
    owner: Option<&Pubkey>,
    rent_sysvar_account_provided: bool,
) -> ProgramResult {
    // Accounts expected depend on whether we have the `rent_sysvar` account or not.

    let (new_account_info, mint_info, owner, remaining) = if let Some(owner) = owner {
        let [new_account_info, mint_info, remaining @ ..] = accounts else {
            return Err(ProgramError::NotEnoughAccountKeys);
        };
        (new_account_info, mint_info, owner, remaining)
    } else {
        let [new_account_info, mint_info, owner_info, remaining @ ..] = accounts else {
            return Err(ProgramError::NotEnoughAccountKeys);
        };
        (new_account_info, mint_info, owner_info.key(), remaining)
    };

    // Check rent-exempt status of the token account.

    let new_account_info_data_len = new_account_info.data_len();

    let minimum_balance = if rent_sysvar_account_provided {
        let rent_sysvar_info = remaining
            .first()
            .ok_or(ProgramError::NotEnoughAccountKeys)?;
        // SAFETY: single immutable borrow to `rent_sysvar_info`; account ID and length
        // are checked by `from_account_info_unchecked`.
        let rent = unsafe { Rent::from_account_info_unchecked(rent_sysvar_info)? };
        rent.minimum_balance(new_account_info_data_len)
    } else {
        Rent::get()?.minimum_balance(new_account_info_data_len)
    };

    let is_native_mint = is_native_mint(mint_info.key());

    // Initialize the account.

    // SAFETY: single mutable borrow of the 'new_account_info' account data.
    let account =
        unsafe { load_mut_unchecked::<Account>(new_account_info.borrow_mut_data_unchecked())? };

    if account.is_initialized()? {
        return Err(TokenError::AlreadyInUse.into());
    }

    if new_account_info.lamports() < minimum_balance {
        return Err(TokenError::NotRentExempt.into());
    }

    if !is_native_mint {
        check_account_owner(mint_info)?;

        // SAFETY: single immutable borrow of `mint_info` account data and
        // `load` validates that the mint is initialized.
        let _ = unsafe {
            load::<Mint>(mint_info.borrow_data_unchecked()).map_err(|_| TokenError::InvalidMint)?
        };
    }

    account.set_account_state(AccountState::Initialized);
    account.mint = *mint_info.key();
    account.owner = *owner;

    if is_native_mint {
        account.set_native(true);
        account.set_native_amount(minimum_balance);
        // `new_account_info` lamports are already checked to be greater than or equal
        // to the minimum balance.
        account.set_amount(new_account_info.lamports() - minimum_balance);
    }

    Ok(())
}
