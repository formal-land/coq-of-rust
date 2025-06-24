//! Cross-program invocation helpers.

use core::{mem::MaybeUninit, ops::Deref, slice::from_raw_parts};

use crate::{
    account_info::{AccountInfo, BorrowState},
    instruction::{Account, Instruction, Signer},
    program_error::ProgramError,
    pubkey::Pubkey,
    ProgramResult,
};

/// Maximum number of accounts that can be passed to a cross-program invocation.
pub const MAX_CPI_ACCOUNTS: usize = 64;

/// Invoke a cross-program instruction from an array of `AccountInfo`s.
///
/// This function is a convenience wrapper around the [`invoke_signed`] function
/// with the signers' seeds set to an empty slice.
///
/// Note that this function is inlined to avoid the overhead of a function call,
/// but uses stack memory allocation. When a large number of accounts is needed,
/// it is recommended to use the [`slice_invoke`] function instead to reduce
/// stack memory utilization.
///
/// # Important
///
/// The accounts on the `account_infos` slice must be in the same order as the
/// `accounts` field of the `instruction`. When the instruction has duplicated
/// accounts, it is necessary to pass a duplicated reference to the same account
/// to maintain the 1:1 relationship between `account_infos` and `accounts`.
#[inline(always)]
pub fn invoke<const ACCOUNTS: usize>(
    instruction: &Instruction,
    account_infos: &[&AccountInfo; ACCOUNTS],
) -> ProgramResult {
    invoke_signed::<ACCOUNTS>(instruction, account_infos, &[])
}

/// Invoke a cross-program instruction from a slice of `AccountInfo`s.
///
/// This function is a convenience wrapper around the [`invoke_signed_with_bounds`]
/// function with the signers' seeds set to an empty slice.
///
/// The `MAX_ACCOUNTS` constant defines the maximum number of accounts expected
/// to be passed to the cross-program invocation. This provides an upper bound to
/// the number of accounts that need to be statically allocated for cases where the
/// number of instruction accounts is not known at compile time. The final number of
/// accounts passed to the cross-program invocation will be the number of accounts
/// required by the `instruction`, even if `MAX_ACCOUNTS` is greater than that. When
/// `MAX_ACCOUNTS` is lower than the number of accounts expected by the instruction,
/// this function will return a [`ProgramError::InvalidArgument`] error.
///
/// Note that this function is inlined to avoid the overhead of a function call,
/// but uses stack memory allocation. When a large number of accounts is needed,
/// it is recommended to use the [`slice_invoke`] function instead to reduce
/// stack memory utilization.
///
/// # Important
///
/// The accounts on the `account_infos` slice must be in the same order as the
/// `accounts` field of the `instruction`. When the instruction has duplicated
/// accounts, it is necessary to pass a duplicated reference to the same account
/// to maintain the 1:1 relationship between `account_infos` and `accounts`.
#[inline(always)]
pub fn invoke_with_bounds<const MAX_ACCOUNTS: usize>(
    instruction: &Instruction,
    account_infos: &[&AccountInfo],
) -> ProgramResult {
    invoke_signed_with_bounds::<MAX_ACCOUNTS>(instruction, account_infos, &[])
}

/// Invoke a cross-program instruction from a slice of `AccountInfo`s.
///
/// This function is a convenience wrapper around the [`slice_invoke_signed`]
/// function with the signers' seeds set to an empty slice.
///
/// Note that the maximum number of accounts that can be passed to a cross-program
/// invocation is defined by the [`MAX_CPI_ACCOUNTS`] constant. Even if the slice
/// of `AccountInfo`s has more accounts, only the number of accounts required by
/// the `instruction` will be used. If the number of accounts required by the
/// instruction is greater than [`MAX_CPI_ACCOUNTS`], this function will return a
/// [`ProgramError::InvalidArgument`] error.
///
/// # Important
///
/// The accounts on the `account_infos` slice must be in the same order as the
/// `accounts` field of the `instruction`. When the instruction has duplicated
/// accounts, it is necessary to pass a duplicated reference to the same account
/// to maintain the 1:1 relationship between `account_infos` and `accounts`.
#[inline(always)]
pub fn slice_invoke(instruction: &Instruction, account_infos: &[&AccountInfo]) -> ProgramResult {
    slice_invoke_signed(instruction, account_infos, &[])
}

/// Invoke a cross-program instruction with signatures from an array of
/// `AccountInfo`s.
///
/// This function performs validation of the `account_infos` slice to ensure that:
///   1. It has at least as many accounts as the number of accounts expected by
///      the instruction.
///   2. The accounts match the expected accounts in the instruction, i.e., their
///      `Pubkey` matches the `pubkey` in the `AccountMeta`.
///   3. The borrow state of the accounts is compatible with the mutability of the
///      accounts in the instruction.
///
/// This validation is done to ensure that the borrow checker rules are followed,
/// consuming CUs in the process. The `invoke_signed_unchecked` is an alternative
/// to this function that have lower CU consumption since it does not perform
/// any validation. This should only be used when the caller is sure that the borrow
/// checker rules are followed.
///
/// Note that this function is inlined to avoid the overhead of a function call,
/// but uses stack memory allocation. When a large number of accounts is needed,
/// it is recommended to use the [`slice_invoke_signed`] function instead to reduce
/// stack memory utilization.
///
/// # Important
///
/// The accounts on the `account_infos` slice must be in the same order as the
/// `accounts` field of the `instruction`. When the instruction has duplicated
/// accounts, it is necessary to pass a duplicated reference to the same account
/// to maintain the 1:1 relationship between `account_infos` and `accounts`.
#[inline(always)]
pub fn invoke_signed<const ACCOUNTS: usize>(
    instruction: &Instruction,
    account_infos: &[&AccountInfo; ACCOUNTS],
    signers_seeds: &[Signer],
) -> ProgramResult {
    // SAFETY: The array of `AccountInfo`s will be checked to ensure that it has
    // the same number of accounts as the instruction – this indirectly validates
    // that the stack allocated account storage `ACCOUNTS` is sufficient for the
    // number of accounts expected by the instruction.
    unsafe {
        inner_invoke_signed_with_bounds::<ACCOUNTS>(instruction, account_infos, signers_seeds)
    }
}

/// Invoke a cross-program instruction with signatures from a slice of
/// `AccountInfo`s.
///
/// This function performs validation of the `account_infos` slice to ensure that:
///   1. It has at least as many accounts as the number of accounts expected by
///      the instruction.
///   2. The accounts match the expected accounts in the instruction, i.e., their
///      `Pubkey` matches the `pubkey` in the `AccountMeta`.
///   3. The borrow state of the accounts is compatible with the mutability of the
///      accounts in the instruction.
///
/// This validation is done to ensure that the borrow checker rules are followed,
/// consuming CUs in the process. The [`invoke_signed_unchecked`] is an alternative
/// to this function that has lower CU consumption since it does not perform
/// any validation. This should only be used when the caller is sure that the borrow
/// checker rules are followed.
///
/// The `MAX_ACCOUNTS` constant defines the maximum number of accounts expected
/// to be passed to the cross-program invocation. This provides an upper bound to
/// the number of accounts that need to be statically allocated for cases where the
/// number of instruction accounts is not known at compile time. The final number of
/// accounts passed to the cross-program invocation will be the number of accounts
/// required by the `instruction`, even if `MAX_ACCOUNTS` is greater than that. When
/// `MAX_ACCOUNTS` is lower than the number of accounts expected by the instruction,
/// this function will return a [`ProgramError::InvalidArgument`] error.
///
/// Note that this function is inlined to avoid the overhead of a function call,
/// but uses stack memory allocation. When a large number of accounts is needed,
/// it is recommended to use the [`slice_invoke_signed`] function instead to reduce
/// stack memory utilization.
///
/// # Important
///
/// The accounts on the `account_infos` slice must be in the same order as the
/// `accounts` field of the `instruction`. When the instruction has duplicated
/// accounts, it is necessary to pass a duplicated reference to the same account
/// to maintain the 1:1 relationship between `account_infos` and `accounts`.
#[inline(always)]
pub fn invoke_signed_with_bounds<const MAX_ACCOUNTS: usize>(
    instruction: &Instruction,
    account_infos: &[&AccountInfo],
    signers_seeds: &[Signer],
) -> ProgramResult {
    // Check that the stack allocated account storage `MAX_ACCOUNTS` is sufficient
    // for the number of accounts expected by the instruction.
    //
    // The check for the slice of `AccountInfo`s not being less than the
    // number of accounts expected by the instruction is done in
    // `invoke_signed_with_bounds`.
    if MAX_ACCOUNTS < instruction.accounts.len() {
        return Err(ProgramError::InvalidArgument);
    }

    // SAFETY: The stack allocated account storage `MAX_ACCOUNTS` was validated.
    unsafe {
        inner_invoke_signed_with_bounds::<MAX_ACCOUNTS>(instruction, account_infos, signers_seeds)
    }
}

/// Invoke a cross-program instruction with signatures from a slice of
/// `AccountInfo`s.
///
/// This function performs validation of the `account_infos` slice to ensure that:
///   1. It has at least as many accounts as the number of accounts expected by
///      the instruction.
///   2. The accounts match the expected accounts in the instruction, i.e., their
///      `Pubkey` matches the `pubkey` in the `AccountMeta`.
///   3. The borrow state of the accounts is compatible with the mutability of the
///      accounts in the instruction.
///
/// This validation is done to ensure that the borrow checker rules are followed,
/// consuming CUs in the process. The [`invoke_signed_unchecked`] is an alternative
/// to this function that have lower CU consumption since it does not perform
/// any validation. This should only be used when the caller is sure that the borrow
/// checker rules are followed.
///
/// Note that the maximum number of accounts that can be passed to a cross-program
/// invocation is defined by the `MAX_CPI_ACCOUNTS` constant. Even if the slice
/// of `AccountInfo`s has more accounts, only the number of accounts required by
/// the `instruction` will be used. If the number of accounts required by the
/// instruction is greater than [`MAX_CPI_ACCOUNTS`], this function will return a
/// [`ProgramError::InvalidArgument`] error.
///
/// # Important
///
/// The accounts on the `account_infos` slice must be in the same order as the
/// `accounts` field of the `instruction`. When the instruction has duplicated
/// accounts, it is necessary to pass a duplicated reference to the same account
/// to maintain the 1:1 relationship between `account_infos` and `accounts`.
pub fn slice_invoke_signed(
    instruction: &Instruction,
    account_infos: &[&AccountInfo],
    signers_seeds: &[Signer],
) -> ProgramResult {
    // Check that the stack allocated account storage `MAX_CPI_ACCOUNTS` is
    // sufficient for the number of accounts expected by the instruction.
    //
    // The check for the slice of `AccountInfo`s not being less than the
    // number of accounts expected by the instruction is done in
    // `invoke_signed_with_bounds`.
    if MAX_CPI_ACCOUNTS < instruction.accounts.len() {
        return Err(ProgramError::InvalidArgument);
    }

    // SAFETY: The stack allocated account storage `MAX_CPI_ACCOUNTS` was validated.
    unsafe {
        inner_invoke_signed_with_bounds::<MAX_CPI_ACCOUNTS>(
            instruction,
            account_infos,
            signers_seeds,
        )
    }
}

/// Internal function to invoke a cross-program instruction with signatures
/// from a slice of `AccountInfo`s performing borrow checking.
///
/// This function performs validation of the `account_infos` slice to ensure that:
///   1. It has at least as many accounts as the number of accounts expected by
///      the instruction.
///   2. The accounts match the expected accounts in the instruction, i.e., their
///      `Pubkey` matches the `pubkey` in the `AccountMeta`.
///   3. The borrow state of the accounts is compatible with the mutability of the
///      accounts in the instruction.
///
/// # Safety
///
/// This function is unsafe because it does not check that the stack allocated account
/// storage `MAX_ACCOUNTS` is sufficient for the number of accounts expected by the
/// instruction. Using a value of `MAX_ACCOUNTS` that is less than the number of accounts
/// expected by the instruction will result in undefined behavior.
#[inline(always)]
unsafe fn inner_invoke_signed_with_bounds<const MAX_ACCOUNTS: usize>(
    instruction: &Instruction,
    account_infos: &[&AccountInfo],
    signers_seeds: &[Signer],
) -> ProgramResult {
    // Check that the number of `MAX_ACCOUNTS` provided is not greater than
    // the maximum number of accounts allowed.
    const {
        assert!(
            MAX_ACCOUNTS <= MAX_CPI_ACCOUNTS,
            "MAX_ACCOUNTS is greater than allowed MAX_CPI_ACCOUNTS"
        );
    }

    // Check that the number of accounts provided is not less than
    // the number of accounts expected by the instruction.
    if account_infos.len() < instruction.accounts.len() {
        return Err(ProgramError::NotEnoughAccountKeys);
    }

    const UNINIT: MaybeUninit<Account> = MaybeUninit::<Account>::uninit();
    let mut accounts = [UNINIT; MAX_ACCOUNTS];

    account_infos
        .iter()
        .zip(instruction.accounts.iter())
        .zip(accounts.iter_mut())
        .try_for_each(|((account_info, account_meta), account)| {
            // In order to check whether the borrow state is compatible
            // with the invocation, we need to check that we have the
            // correct account info and meta pair.
            if account_info.key() != account_meta.pubkey {
                return Err(ProgramError::InvalidArgument);
            }

            // Determines the borrow state that would be invalid according
            // to their mutability on the instruction.
            let invalid_state = if account_meta.is_writable {
                // If the account is required to be writable, it cannot
                //  be currently borrowed.
                BorrowState::Borrowed
            } else {
                // If the account is required to be read-only, it cannot
                // be currently mutably borrowed.
                BorrowState::MutablyBorrowed
            };

            if account_info.is_borrowed(invalid_state) {
                return Err(ProgramError::AccountBorrowFailed);
            }

            account.write(Account::from(*account_info));

            Ok(())
        })?;

    // SAFETY: At this point it is guaranteed that account infos are borrowable
    // according to their mutability on the instruction.
    unsafe {
        invoke_signed_unchecked(
            instruction,
            from_raw_parts(accounts.as_ptr() as _, instruction.accounts.len()),
            signers_seeds,
        );
    }

    Ok(())
}

/// Invoke a cross-program instruction but don't enforce Rust's aliasing rules.
///
/// This function does not check that [`Account`]s are properly borrowable.
/// Those checks consume CUs that this function avoids.
///
/// Note that the maximum number of accounts that can be passed to a cross-program
/// invocation is defined by the `MAX_CPI_ACCOUNTS` constant. Even if the slice
/// of `AccountInfo`s has more accounts, only the number of accounts required by
/// the `instruction` will be used.
///
/// # Safety
///
/// If any of the writable accounts passed to the callee contain data that is
/// borrowed within the calling program, and that data is written to by the
/// callee, then Rust's aliasing rules will be violated and cause undefined
/// behavior.
#[inline(always)]
pub unsafe fn invoke_unchecked(instruction: &Instruction, accounts: &[Account]) {
    invoke_signed_unchecked(instruction, accounts, &[])
}

/// Invoke a cross-program instruction with signatures but don't enforce Rust's
/// aliasing rules.
///
/// This function does not check that [`Account`]s are properly borrowable.
/// Those checks consume CUs that this function avoids.
///
/// Note that the maximum number of accounts that can be passed to a cross-program
/// invocation is defined by the `MAX_CPI_ACCOUNTS` constant. Even if the slice
/// of `AccountInfo`s has more accounts, only the number of accounts required by
/// the `instruction` will be used.
///
/// # Safety
///
/// If any of the writable accounts passed to the callee contain data that is
/// borrowed within the calling program, and that data is written to by the
/// callee, then Rust's aliasing rules will be violated and cause undefined
/// behavior.
#[inline(always)]
pub unsafe fn invoke_signed_unchecked(
    instruction: &Instruction,
    accounts: &[Account],
    signers_seeds: &[Signer],
) {
    #[cfg(target_os = "solana")]
    {
        use crate::instruction::AccountMeta;

        /// An `Instruction` as expected by `sol_invoke_signed_c`.
        ///
        /// DO NOT EXPOSE THIS STRUCT:
        ///
        /// To ensure pointers are valid upon use, the scope of this struct should
        /// only be limited to the stack where sol_invoke_signed_c happens and then
        /// discarded immediately after.
        #[repr(C)]
        struct CInstruction<'a> {
            /// Public key of the program.
            program_id: *const Pubkey,

            /// Accounts expected by the program instruction.
            accounts: *const AccountMeta<'a>,

            /// Number of accounts expected by the program instruction.
            accounts_len: u64,

            /// Data expected by the program instruction.
            data: *const u8,

            /// Length of the data expected by the program instruction.
            data_len: u64,
        }

        let cpi_instruction = CInstruction {
            program_id: instruction.program_id,
            accounts: instruction.accounts.as_ptr(),
            accounts_len: instruction.accounts.len() as u64,
            data: instruction.data.as_ptr(),
            data_len: instruction.data.len() as u64,
        };

        unsafe {
            crate::syscalls::sol_invoke_signed_c(
                &cpi_instruction as *const _ as *const u8,
                accounts as *const _ as *const u8,
                accounts.len() as u64,
                signers_seeds as *const _ as *const u8,
                signers_seeds.len() as u64,
            )
        };
    }

    #[cfg(not(target_os = "solana"))]
    core::hint::black_box((instruction, accounts, signers_seeds));
}

/// Maximum size that can be set using [`set_return_data`].
pub const MAX_RETURN_DATA: usize = 1024;

/// Set the running program's return data.
///
/// Return data is a dedicated per-transaction buffer for data passed
/// from cross-program invoked programs back to their caller.
///
/// The maximum size of return data is [`MAX_RETURN_DATA`]. Return data is
/// retrieved by the caller with [`get_return_data`].
#[inline(always)]
pub fn set_return_data(data: &[u8]) {
    #[cfg(target_os = "solana")]
    unsafe {
        crate::syscalls::sol_set_return_data(data.as_ptr(), data.len() as u64)
    };

    #[cfg(not(target_os = "solana"))]
    core::hint::black_box(data);
}

/// Get the return data from an invoked program.
///
/// For every transaction there is a single buffer with maximum length
/// [`MAX_RETURN_DATA`], paired with a [`Pubkey`] representing the program ID of
/// the program that most recently set the return data. Thus the return data is
/// a global resource and care must be taken to ensure that it represents what
/// is expected: called programs are free to set or not set the return data; and
/// the return data may represent values set by programs multiple calls down the
/// call stack, depending on the circumstances of transaction execution.
///
/// Return data is set by the callee with [`set_return_data`].
///
/// Return data is cleared before every CPI invocation &mdash; a program that
/// has invoked no other programs can expect the return data to be `None`; if no
/// return data was set by the previous CPI invocation, then this function
/// returns `None`.
///
/// Return data is not cleared after returning from CPI invocations &mdash; a
/// program that has called another program may retrieve return data that was
/// not set by the called program, but instead set by a program further down the
/// call stack; or, if a program calls itself recursively, it is possible that
/// the return data was not set by the immediate call to that program, but by a
/// subsequent recursive call to that program. Likewise, an external RPC caller
/// may see return data that was not set by the program it is directly calling,
/// but by a program that program called.
///
/// For more about return data see the [documentation for the return data proposal][rdp].
///
/// [rdp]: https://docs.solanalabs.com/proposals/return-data
#[inline]
pub fn get_return_data() -> Option<ReturnData> {
    #[cfg(target_os = "solana")]
    {
        const UNINIT_BYTE: core::mem::MaybeUninit<u8> = core::mem::MaybeUninit::<u8>::uninit();
        let mut data = [UNINIT_BYTE; MAX_RETURN_DATA];
        let mut program_id = MaybeUninit::<Pubkey>::uninit();

        let size = unsafe {
            crate::syscalls::sol_get_return_data(
                data.as_mut_ptr() as *mut u8,
                data.len() as u64,
                program_id.as_mut_ptr() as *mut Pubkey,
            )
        };

        if size == 0 {
            None
        } else {
            Some(ReturnData {
                program_id: unsafe { program_id.assume_init() },
                data,
                size: core::cmp::min(size as usize, MAX_RETURN_DATA),
            })
        }
    }

    #[cfg(not(target_os = "solana"))]
    core::hint::black_box(None)
}

/// Struct to hold the return data from an invoked program.
pub struct ReturnData {
    /// Program that most recently set the return data.
    program_id: Pubkey,

    /// Return data set by the program.
    data: [MaybeUninit<u8>; MAX_RETURN_DATA],

    /// Length of the return data.
    size: usize,
}

impl ReturnData {
    /// Returns the program that most recently set the return data.
    pub fn program_id(&self) -> &Pubkey {
        &self.program_id
    }

    /// Return the data set by the program.
    pub fn as_slice(&self) -> &[u8] {
        unsafe { from_raw_parts(self.data.as_ptr() as _, self.size) }
    }
}

impl Deref for ReturnData {
    type Target = [u8];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}
