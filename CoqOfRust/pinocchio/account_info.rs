//! Data structures to represent account information.

use core::{
    marker::PhantomData,
    mem::ManuallyDrop,
    ptr::NonNull,
    slice::{from_raw_parts, from_raw_parts_mut},
};

#[cfg(target_os = "solana")]
use crate::syscalls::sol_memset_;

use crate::{program_error::ProgramError, pubkey::Pubkey, ProgramResult};

/// Maximum number of bytes a program may add to an account during a
/// single top-level instruction.
pub const MAX_PERMITTED_DATA_INCREASE: usize = 1_024 * 10;

/// Represents masks for borrow state of an account.
#[repr(u8)]
#[derive(Clone, Copy)]
pub enum BorrowState {
    /// Mask to check whether an account is already borrowed.
    ///
    /// This will test both data and lamports borrow state.
    Borrowed = 0b_1111_1111,

    /// Mask to check whether an account is already mutably borrowed.
    ///
    /// This will test both data and lamports mutable borrow state.
    MutablyBorrowed = 0b_1000_1000,
}

/// Raw account data.
///
/// This data is wrapped in an `AccountInfo` struct, which provides safe access
/// to the data.
#[repr(C)]
#[derive(Clone, Copy, Default)]
pub(crate) struct Account {
    /// Borrow state for lamports and account data.
    ///
    /// This reuses the memory reserved for the duplicate flag in the
    /// account to track lamports and data borrows. It represents the
    /// numbers of borrows available.
    ///
    /// Bits in the borrow byte are used as follows:
    ///
    ///   * lamport mutable borrow flag
    ///     - `7 6 5 4 3 2 1 0`
    ///     - `x . . . . . . .`: `1` -> the lamport field can be mutably borrowed;
    ///       `0` -> there is an outstanding mutable borrow for the lamports.
    ///
    ///   * lamport immutable borrow count
    ///     - `7 6 5 4 3 2 1 0`
    ///     - `. x x x . . . .`: number of immutable borrows that can still be
    ///       allocated, for the lamports field. Ranges from 7 (`111`) to
    ///        0 (`000`).
    ///
    ///   * data mutable borrow flag
    ///     - `7 6 5 4 3 2 1 0`
    ///     - `. . . . x . . .`:  `1` -> the account data can be mutably borrowed;
    ///       `0` -> there is an outstanding mutable borrow for the account data.
    ///
    ///   * data immutable borrow count
    ///     - `7 6 5 4 3 2 1 0`
    ///     - `. . . . . x x x`: Number of immutable borrows that can still be
    ///       allocated, for the account data. Ranges from 7 (`111`) to 0 (`000`).
    ///
    /// Note that this values are shared across `AccountInfo`s over the
    /// same account, e.g., in case of duplicated accounts, they share
    /// the same borrow state.
    pub(crate) borrow_state: u8,

    /// Indicates whether the transaction was signed by this account.
    is_signer: u8,

    /// Indicates whether the account is writable.
    is_writable: u8,

    /// Indicates whether this account represents a program.
    executable: u8,

    /// Difference between the original data length and the current
    /// data length.
    ///
    /// This is used to track the original data length of the account
    /// when the account is resized. The runtime guarantees that this
    /// value is zero at the start of the instruction.
    resize_delta: i32,

    /// Public key of the account.
    key: Pubkey,

    /// Program that owns this account. Modifiable by programs.
    owner: Pubkey,

    /// The lamports in the account. Modifiable by programs.
    lamports: u64,

    /// Length of the data. Modifiable by programs.
    pub(crate) data_len: u64,
}

/// Wrapper struct for an `Account`.
///
/// This struct provides safe access to the data in an `Account`. It is also
/// used to track borrows of the account data and lamports, given that an
/// account can be "shared" across multiple `AccountInfo` instances.
#[repr(C)]
#[derive(Clone, PartialEq, Eq)]
pub struct AccountInfo {
    /// Raw (pointer to) account data.
    ///
    /// Note that this is a pointer can be shared across multiple `AccountInfo`.
    pub(crate) raw: *mut Account,
}

impl AccountInfo {
    /// Public key of the account.
    #[inline(always)]
    pub fn key(&self) -> &Pubkey {
        unsafe { &(*self.raw).key }
    }

    /// Program that owns this account.
    ///
    /// # Safety
    ///
    /// A reference returned by this method is invalidated when [`Self::assign`]
    /// is called.
    #[inline(always)]
    pub unsafe fn owner(&self) -> &Pubkey {
        &(*self.raw).owner
    }

    /// Indicates whether the transaction was signed by this account.
    #[inline(always)]
    pub fn is_signer(&self) -> bool {
        unsafe { (*self.raw).is_signer != 0 }
    }

    /// Indicates whether the account is writable.
    #[inline(always)]
    pub fn is_writable(&self) -> bool {
        unsafe { (*self.raw).is_writable != 0 }
    }

    /// Indicates whether this account represents a program.
    ///
    /// Program accounts are always read-only.
    #[inline(always)]
    pub fn executable(&self) -> bool {
        unsafe { (*self.raw).executable != 0 }
    }

    /// Returns the size of the data in the account.
    #[inline(always)]
    pub fn data_len(&self) -> usize {
        unsafe { (*self.raw).data_len as usize }
    }

    /// Returns the delta between the original data length and the current
    /// data length.
    ///
    /// This value will be different than zero if the account has been resized
    /// during the current instruction.
    #[inline(always)]
    pub fn resize_delta(&self) -> i32 {
        unsafe { (*self.raw).resize_delta }
    }

    /// Returns the lamports in the account.
    #[inline(always)]
    pub fn lamports(&self) -> u64 {
        unsafe { (*self.raw).lamports }
    }

    /// Indicates whether the account data is empty.
    ///
    /// An account is considered empty if the data length is zero.
    #[inline(always)]
    pub fn data_is_empty(&self) -> bool {
        self.data_len() == 0
    }

    /// Checks if the account is owned by the given program.
    #[inline(always)]
    pub fn is_owned_by(&self, program: &Pubkey) -> bool {
        unsafe { &(*self.raw).owner == program }
    }

    /// Changes the owner of the account.
    ///
    /// # Safety
    ///
    /// Using this method invalidates any reference returned by [`Self::owner`].
    #[inline(always)]
    pub unsafe fn assign(&self, new_owner: &Pubkey) {
        #[allow(invalid_reference_casting)]
        core::ptr::write_volatile(&(*self.raw).owner as *const _ as *mut Pubkey, *new_owner);
    }

    /// Return true if the account borrow state is set to the given state.
    ///
    /// This will test both data and lamports borrow state.
    #[inline(always)]
    pub fn is_borrowed(&self, state: BorrowState) -> bool {
        let borrow_state = unsafe { (*self.raw).borrow_state };
        let mask = state as u8;
        // If borrow state has any of the state bits of the mask not set,
        // then the account is borrowed for that state.
        (borrow_state & mask) != mask
    }

    /// Returns a read-only reference to the lamports in the account.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it does not return a `Ref`, thus leaving the borrow
    /// flag untouched. Useful when an instruction has verified non-duplicate accounts.
    #[inline(always)]
    pub unsafe fn borrow_lamports_unchecked(&self) -> &u64 {
        &(*self.raw).lamports
    }

    /// Returns a mutable reference to the lamports in the account.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it does not return a `Ref`, thus leaving the borrow
    /// flag untouched. Useful when an instruction has verified non-duplicate accounts.
    #[allow(clippy::mut_from_ref)]
    #[inline(always)]
    pub unsafe fn borrow_mut_lamports_unchecked(&self) -> &mut u64 {
        &mut (*self.raw).lamports
    }

    /// Returns a read-only reference to the data in the account.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it does not return a `Ref`, thus leaving the borrow
    /// flag untouched. Useful when an instruction has verified non-duplicate accounts.
    #[inline(always)]
    pub unsafe fn borrow_data_unchecked(&self) -> &[u8] {
        core::slice::from_raw_parts(self.data_ptr(), self.data_len())
    }

    /// Returns a mutable reference to the data in the account.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it does not return a `Ref`, thus leaving the borrow
    /// flag untouched. Useful when an instruction has verified non-duplicate accounts.
    #[allow(clippy::mut_from_ref)]
    #[inline(always)]
    pub unsafe fn borrow_mut_data_unchecked(&self) -> &mut [u8] {
        core::slice::from_raw_parts_mut(self.data_ptr(), self.data_len())
    }

    /// Tries to get a read-only reference to the lamport field, failing if the
    /// field is already mutable borrowed or if 7 borrows already exist.
    pub fn try_borrow_lamports(&self) -> Result<Ref<u64>, ProgramError> {
        // check if the account lamports are already borrowed
        self.can_borrow_lamports()?;

        let borrow_state = self.raw as *mut u8;
        // SAFETY: The `borrow_state` is a mutable pointer to the borrow state
        // of the account, which is guaranteed to be valid.
        //
        // "consumes" one immutable borrow for lamports; we are guaranteed
        // that there is at least one immutable borrow available.
        unsafe { *borrow_state -= 1 << LAMPORTS_SHIFT };

        // return the reference to lamports
        Ok(Ref {
            value: unsafe { NonNull::from(&(*self.raw).lamports) },
            state: unsafe { NonNull::new_unchecked(borrow_state) },
            borrow_shift: LAMPORTS_SHIFT,
            marker: PhantomData,
        })
    }

    /// Tries to get a read only reference to the lamport field, failing if the field
    /// is already borrowed in any form.
    pub fn try_borrow_mut_lamports(&self) -> Result<RefMut<u64>, ProgramError> {
        // check if the account lamports are already borrowed
        self.can_borrow_mut_lamports()?;

        let borrow_state = self.raw as *mut u8;
        // SAFETY: The `borrow_state` is a mutable pointer to the borrow state
        // of the account, which is guaranteed to be valid.
        //
        // "consumes" the mutable borrow for lamports; we are guaranteed
        // that lamports are not already borrowed in any form
        unsafe { *borrow_state &= 0b_0111_1111 };

        // return the mutable reference to lamports
        Ok(RefMut {
            value: unsafe { NonNull::from(&mut (*self.raw).lamports) },
            state: unsafe { NonNull::new_unchecked(borrow_state) },
            borrow_mask: LAMPORTS_MASK,
            marker: PhantomData,
        })
    }

    /// Checks if it is possible to get a read-only reference to the lamport field,
    /// failing if the field is already mutable borrowed or if 7 borrows already exist.
    #[deprecated(since = "0.8.4", note = "Use `can_borrow_lamports` instead")]
    #[inline(always)]
    pub fn check_borrow_lamports(&self) -> Result<(), ProgramError> {
        self.can_borrow_lamports()
    }

    /// Checks if it is possible to get a read-only reference to the lamport field,
    /// failing if the field is already mutable borrowed or if `7` borrows already exist.
    #[inline(always)]
    pub fn can_borrow_lamports(&self) -> Result<(), ProgramError> {
        let borrow_state = unsafe { (*self.raw).borrow_state };

        // check if mutable borrow is already taken
        if borrow_state & 0b_1000_0000 != 0b_1000_0000 {
            return Err(ProgramError::AccountBorrowFailed);
        }

        // check if we have reached the max immutable borrow count
        if borrow_state & 0b_0111_0000 == 0 {
            return Err(ProgramError::AccountBorrowFailed);
        }

        Ok(())
    }

    /// Checks if it is possible to get a mutable reference to the lamport field,
    /// failing if the field is already borrowed in any form.
    #[deprecated(since = "0.8.4", note = "Use `can_borrow_mut_lamports` instead")]
    #[inline(always)]
    pub fn check_borrow_mut_lamports(&self) -> Result<(), ProgramError> {
        self.can_borrow_mut_lamports()
    }

    /// Checks if it is possible to get a mutable reference to the lamport field,
    /// failing if the field is already borrowed in any form.
    #[inline(always)]
    pub fn can_borrow_mut_lamports(&self) -> Result<(), ProgramError> {
        let borrow_state = unsafe { (*self.raw).borrow_state };

        // check if any borrow (mutable or immutable) is already taken for lamports
        if borrow_state & 0b_1111_0000 != 0b_1111_0000 {
            return Err(ProgramError::AccountBorrowFailed);
        }

        Ok(())
    }

    /// Tries to get a read-only reference to the data field, failing if the field
    /// is already mutable borrowed or if `7` borrows already exist.
    pub fn try_borrow_data(&self) -> Result<Ref<[u8]>, ProgramError> {
        // check if the account data is already borrowed
        self.can_borrow_data()?;

        let borrow_state = self.raw as *mut u8;
        // SAFETY: The `borrow_state` is a mutable pointer to the borrow state
        // of the account, which is guaranteed to be valid.
        //
        // "consumes" one immutable borrow for data; we are guaranteed
        // that there is at least one immutable borrow available
        unsafe { *borrow_state -= 1 };

        // return the reference to data
        Ok(Ref {
            value: unsafe { NonNull::from(from_raw_parts(self.data_ptr(), self.data_len())) },
            state: unsafe { NonNull::new_unchecked(borrow_state) },
            borrow_shift: DATA_SHIFT,
            marker: PhantomData,
        })
    }

    /// Tries to get a mutable reference to the data field, failing if the field
    /// is already borrowed in any form.
    pub fn try_borrow_mut_data(&self) -> Result<RefMut<[u8]>, ProgramError> {
        // check if the account data is already borrowed
        self.can_borrow_mut_data()?;

        let borrow_state = self.raw as *mut u8;
        // SAFETY: The `borrow_state` is a mutable pointer to the borrow state
        // of the account, which is guaranteed to be valid.
        //
        // "consumes" the mutable borrow for account data; we are guaranteed
        // that account data are not already borrowed in any form
        unsafe { *borrow_state &= 0b_1111_0111 };

        // return the mutable reference to data
        Ok(RefMut {
            value: unsafe { NonNull::from(from_raw_parts_mut(self.data_ptr(), self.data_len())) },
            state: unsafe { NonNull::new_unchecked(borrow_state) },
            borrow_mask: DATA_MASK,
            marker: PhantomData,
        })
    }

    /// Checks if it is possible to get a read-only reference to the data field, failing
    /// if the field is already mutable borrowed or if 7 borrows already exist.
    #[deprecated(since = "0.8.4", note = "Use `can_borrow_data` instead")]
    #[inline(always)]
    pub fn check_borrow_data(&self) -> Result<(), ProgramError> {
        self.can_borrow_data()
    }

    /// Checks if it is possible to get a read-only reference to the data field, failing
    /// if the field is already mutable borrowed or if 7 borrows already exist.
    #[inline(always)]
    pub fn can_borrow_data(&self) -> Result<(), ProgramError> {
        let borrow_state = unsafe { (*self.raw).borrow_state };

        // check if mutable data borrow is already taken (most significant bit
        // of the data borrow state)
        if borrow_state & 0b_0000_1000 == 0 {
            return Err(ProgramError::AccountBorrowFailed);
        }

        // check if we have reached the max immutable data borrow count (7)
        if borrow_state & 0b_0000_0111 == 0 {
            return Err(ProgramError::AccountBorrowFailed);
        }

        Ok(())
    }

    /// Checks if it is possible to get a mutable reference to the data field, failing
    /// if the field is already borrowed in any form.
    #[deprecated(since = "0.8.4", note = "Use `can_borrow_mut_data` instead")]
    #[inline(always)]
    pub fn check_borrow_mut_data(&self) -> Result<(), ProgramError> {
        self.can_borrow_mut_data()
    }

    /// Checks if it is possible to get a mutable reference to the data field, failing
    /// if the field is already borrowed in any form.
    #[inline(always)]
    pub fn can_borrow_mut_data(&self) -> Result<(), ProgramError> {
        let borrow_state = unsafe { (*self.raw).borrow_state };

        // check if any borrow (mutable or immutable) is already taken for data
        if borrow_state & 0b_0000_1111 != 0b_0000_1111 {
            return Err(ProgramError::AccountBorrowFailed);
        }

        Ok(())
    }

    /// Realloc the account's data and optionally zero-initialize the new
    /// memory.
    ///
    /// The account data can be increased by up to [`MAX_PERMITTED_DATA_INCREASE`] bytes
    /// within an instruction.
    ///
    /// # Important
    ///
    /// Memory used to grow is already zero-initialized upon program
    /// entrypoint and re-zeroing it wastes compute units. If within the same
    /// call a program reallocs from larger to smaller and back to larger again
    /// the new space could contain stale data. Pass `true` for `zero_init` in
    /// this case, otherwise compute units will be wasted re-zero-initializing.
    ///
    /// Note that `zero_init` being `false` will not be supported by the
    /// program runtime in the future. Programs should not rely on being able to
    /// access stale data and use [`Self::resize`] instead.
    ///
    /// # Safety
    ///
    /// This method makes assumptions about the layout and location of memory
    /// referenced by `AccountInfo` fields. It should only be called for
    /// instances of `AccountInfo` that were created by the runtime and received
    /// in the `process_instruction` entrypoint of a program.
    #[deprecated(since = "0.9.0", note = "Use AccountInfo::resize() instead")]
    pub fn realloc(&self, new_len: usize, zero_init: bool) -> Result<(), ProgramError> {
        // Check wheather the account data is already borrowed.
        self.can_borrow_mut_data()?;

        // Account length is always `< i32::MAX`...
        let current_len = self.data_len() as i32;
        // ...so the new length must fit in an `i32`.
        let new_len = i32::try_from(new_len).map_err(|_| ProgramError::InvalidRealloc)?;

        // Return early if length hasn't changed.
        if new_len == current_len {
            return Ok(());
        }

        let difference = new_len - current_len;
        let accumulated_resize_delta = self.resize_delta() + difference;

        // Return an error when the length increase from the original serialized data
        // length is too large and would result in an out of bounds allocation
        if accumulated_resize_delta > MAX_PERMITTED_DATA_INCREASE as i32 {
            return Err(ProgramError::InvalidRealloc);
        }

        unsafe {
            (*self.raw).data_len = new_len as u64;
            (*self.raw).resize_delta = accumulated_resize_delta;
        }

        if zero_init && difference > 0 {
            unsafe {
                #[cfg(target_os = "solana")]
                sol_memset_(
                    self.data_ptr().add(current_len as usize),
                    0,
                    difference as u64,
                );
                #[cfg(not(target_os = "solana"))]
                core::ptr::write_bytes(
                    self.data_ptr().add(current_len as usize),
                    0,
                    difference as usize,
                );
            }
        }

        Ok(())
    }

    /// Resize (either truncating or zero extending) the account's data.
    ///
    /// The account data can be increased by up to [`MAX_PERMITTED_DATA_INCREASE`] bytes
    /// within an instruction.
    ///
    /// # Important
    ///
    /// This method makes assumptions about the layout and location of memory
    /// referenced by `AccountInfo` fields. It should only be called for
    /// instances of `AccountInfo` that were created by the runtime and received
    /// in the `process_instruction` entrypoint of a program.
    #[inline]
    pub fn resize(&self, new_len: usize) -> Result<(), ProgramError> {
        #[allow(deprecated)]
        self.realloc(new_len, true)
    }

    /// Zero out the the account's data length, lamports and owner fields, effectively
    /// closing the account.
    ///
    /// Note: This does not zero the account data. The account data will be zeroed by
    /// the runtime at the end of the instruction where the account was closed or at the
    /// next CPI call.
    ///
    /// # Important
    ///
    /// The lamports must be moved from the account prior to closing it to prevent
    /// an unbalanced instruction error.
    #[inline]
    pub fn close(&self) -> ProgramResult {
        // make sure the account is not borrowed since we are about to
        // resize the data to zero
        if self.is_borrowed(BorrowState::Borrowed) {
            return Err(ProgramError::AccountBorrowFailed);
        }

        // SAFETY: The are no active borrows on the account data or lamports.
        unsafe {
            // Update the resize delta since closing an account will set its data length
            // to zero (account length is always `< i32::MAX`).
            (*self.raw).resize_delta = self.resize_delta() - self.data_len() as i32;

            self.close_unchecked();
        }

        Ok(())
    }

    /// Zero out the the account's data length, lamports and owner fields, effectively
    /// closing the account.
    ///
    /// Note: This does not zero the account data. The account data will be zeroed by
    /// the runtime at the end of the instruction where the account was closed or at the
    /// next CPI call.
    ///
    /// # Important
    ///
    /// The lamports must be moved from the account prior to closing it to prevent
    /// an unbalanced instruction error.
    ///
    /// If [`Self::realloc`] or [`Self::resize`] are called after closing the account,
    /// they might incorrectly return an error for going over the limit if the account
    /// previously had space allocated since this method does not update the
    /// [`Self::resize_delta`] value.
    ///
    /// # Safety
    ///
    /// This method is unsafe because it does not check if the account data is already
    /// borrowed. It should only be called when the account is not being used.
    ///
    /// It also makes assumptions about the layout and location of memory
    /// referenced by `AccountInfo` fields. It should only be called for
    /// instances of `AccountInfo` that were created by the runtime and received
    /// in the `process_instruction` entrypoint of a program.
    #[inline(always)]
    pub unsafe fn close_unchecked(&self) {
        // We take advantage that the 48 bytes before the account data are:
        // - 32 bytes for the owner
        // - 8 bytes for the lamports
        // - 8 bytes for the data_len
        //
        // So we can zero out them directly.
        #[cfg(target_os = "solana")]
        sol_memset_(self.data_ptr().sub(48), 0, 48);
    }

    /// Returns the memory address of the account data.
    fn data_ptr(&self) -> *mut u8 {
        unsafe { (self.raw as *mut u8).add(core::mem::size_of::<Account>()) }
    }
}

/// Bytes to shift to get to the borrow state of lamports.
const LAMPORTS_SHIFT: u8 = 4;

/// Bytes to shift to get to the borrow state of data.
const DATA_SHIFT: u8 = 0;

/// Reference to account data or lamports with checked borrow rules.
pub struct Ref<'a, T: ?Sized> {
    value: NonNull<T>,
    state: NonNull<u8>,
    /// Indicates the type of borrow (lamports or data) by representing the
    /// shift amount.
    borrow_shift: u8,
    /// The `value` raw pointer is only valid while the `&'a T` lives so we claim
    /// to hold a reference to it.
    marker: PhantomData<&'a T>,
}

impl<'a, T: ?Sized> Ref<'a, T> {
    /// Maps a reference to a new type.
    #[inline]
    pub fn map<U: ?Sized, F>(orig: Ref<'a, T>, f: F) -> Ref<'a, U>
    where
        F: FnOnce(&T) -> &U,
    {
        // Avoid decrementing the borrow flag on Drop.
        let orig = ManuallyDrop::new(orig);

        Ref {
            value: NonNull::from(f(&*orig)),
            state: orig.state,
            borrow_shift: orig.borrow_shift,
            marker: PhantomData,
        }
    }

    /// Filters and maps a reference to a new type.
    #[inline]
    pub fn filter_map<U: ?Sized, F>(orig: Ref<'a, T>, f: F) -> Result<Ref<'a, U>, Self>
    where
        F: FnOnce(&T) -> Option<&U>,
    {
        // Avoid decrementing the borrow flag on Drop.
        let orig = ManuallyDrop::new(orig);

        match f(&*orig) {
            Some(value) => Ok(Ref {
                value: NonNull::from(value),
                state: orig.state,
                borrow_shift: orig.borrow_shift,
                marker: PhantomData,
            }),
            None => Err(ManuallyDrop::into_inner(orig)),
        }
    }
}

impl<T: ?Sized> core::ops::Deref for Ref<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { self.value.as_ref() }
    }
}

impl<T: ?Sized> Drop for Ref<'_, T> {
    // decrement the immutable borrow count
    fn drop(&mut self) {
        unsafe { *self.state.as_mut() += 1 << self.borrow_shift };
    }
}

/// Mask representing the mutable borrow flag for lamports.
const LAMPORTS_MASK: u8 = 0b_1000_0000;

/// Mask representing the mutable borrow flag for data.
const DATA_MASK: u8 = 0b_0000_1000;

/// Mutable reference to account data or lamports with checked borrow rules.
pub struct RefMut<'a, T: ?Sized> {
    value: NonNull<T>,
    state: NonNull<u8>,
    /// Indicates the type of borrow (lamports or data) by representing the
    /// mutable borrow mask.
    borrow_mask: u8,
    /// The `value` raw pointer is only valid while the `&'a T` lives so we claim
    /// to hold a reference to it.
    marker: PhantomData<&'a mut T>,
}

impl<'a, T: ?Sized> RefMut<'a, T> {
    /// Maps a mutable reference to a new type.
    #[inline]
    pub fn map<U: ?Sized, F>(orig: RefMut<'a, T>, f: F) -> RefMut<'a, U>
    where
        F: FnOnce(&mut T) -> &mut U,
    {
        // Avoid decrementing the borrow flag on Drop.
        let mut orig = ManuallyDrop::new(orig);

        RefMut {
            value: NonNull::from(f(&mut *orig)),
            state: orig.state,
            borrow_mask: orig.borrow_mask,
            marker: PhantomData,
        }
    }

    /// Filters and maps a mutable reference to a new type.
    #[inline]
    pub fn filter_map<U: ?Sized, F>(orig: RefMut<'a, T>, f: F) -> Result<RefMut<'a, U>, Self>
    where
        F: FnOnce(&mut T) -> Option<&mut U>,
    {
        // Avoid decrementing the mutable borrow flag on Drop.
        let mut orig = ManuallyDrop::new(orig);

        match f(&mut *orig) {
            Some(value) => {
                let value = NonNull::from(value);
                Ok(RefMut {
                    value,
                    state: orig.state,
                    borrow_mask: orig.borrow_mask,
                    marker: PhantomData,
                })
            }
            None => Err(ManuallyDrop::into_inner(orig)),
        }
    }
}

impl<T: ?Sized> core::ops::Deref for RefMut<'_, T> {
    type Target = T;
    fn deref(&self) -> &Self::Target {
        unsafe { self.value.as_ref() }
    }
}
impl<T: ?Sized> core::ops::DerefMut for RefMut<'_, T> {
    fn deref_mut(&mut self) -> &mut <Self as core::ops::Deref>::Target {
        unsafe { self.value.as_mut() }
    }
}

impl<T: ?Sized> Drop for RefMut<'_, T> {
    fn drop(&mut self) {
        // unset the mutable borrow flag
        unsafe { *self.state.as_mut() |= self.borrow_mask };
    }
}

#[cfg(test)]
mod tests {
    use core::mem::{size_of, MaybeUninit};

    use crate::NON_DUP_MARKER as NOT_BORROWED;

    use super::*;

    #[test]
    fn test_data_ref() {
        let data: [u8; 4] = [0, 1, 2, 3];
        let mut state = NOT_BORROWED - (1 << DATA_SHIFT);

        let ref_data = Ref {
            value: NonNull::from(&data),
            borrow_shift: DATA_SHIFT,
            // borrow state must be a mutable reference
            state: NonNull::from(&mut state),
            marker: PhantomData,
        };

        let new_ref = Ref::map(ref_data, |data| &data[1]);

        assert_eq!(state, NOT_BORROWED - (1 << DATA_SHIFT));
        assert_eq!(*new_ref, 1);

        let Ok(new_ref) = Ref::filter_map(new_ref, |_| Some(&3)) else {
            unreachable!()
        };

        assert_eq!(state, NOT_BORROWED - (1 << DATA_SHIFT));
        assert_eq!(*new_ref, 3);

        let new_ref = Ref::filter_map(new_ref, |_| Option::<&u8>::None);

        assert_eq!(state, NOT_BORROWED - (1 << DATA_SHIFT));
        assert!(new_ref.is_err());

        drop(new_ref);

        assert_eq!(state, NOT_BORROWED);
    }

    #[test]
    fn test_lamports_ref() {
        let lamports: u64 = 10000;
        let mut state = NOT_BORROWED - (1 << LAMPORTS_SHIFT);

        let ref_lamports = Ref {
            value: NonNull::from(&lamports),
            borrow_shift: LAMPORTS_SHIFT,
            // borrow state must be a mutable reference
            state: NonNull::from(&mut state),
            marker: PhantomData,
        };

        let new_ref = Ref::map(ref_lamports, |_| &1000);

        assert_eq!(state, NOT_BORROWED - (1 << LAMPORTS_SHIFT));
        assert_eq!(*new_ref, 1000);

        let Ok(new_ref) = Ref::filter_map(new_ref, |_| Some(&2000)) else {
            unreachable!()
        };

        assert_eq!(state, NOT_BORROWED - (1 << LAMPORTS_SHIFT));
        assert_eq!(*new_ref, 2000);

        let new_ref = Ref::filter_map(new_ref, |_| Option::<&i32>::None);

        assert_eq!(state, NOT_BORROWED - (1 << LAMPORTS_SHIFT));
        assert!(new_ref.is_err());

        drop(new_ref);

        assert_eq!(state, NOT_BORROWED);
    }

    #[test]
    fn test_data_ref_mut() {
        let mut data: [u8; 4] = [0, 1, 2, 3];
        let mut state = 0b_1111_0111;

        let ref_data = RefMut {
            value: NonNull::from(&mut data),
            borrow_mask: DATA_MASK,
            // borrow state must be a mutable reference
            state: NonNull::from(&mut state),
            marker: PhantomData,
        };

        let Ok(mut new_ref) = RefMut::filter_map(ref_data, |data| data.get_mut(0)) else {
            unreachable!()
        };

        *new_ref = 4;

        assert_eq!(state, 0b_1111_0111);
        assert_eq!(*new_ref, 4);

        drop(new_ref);

        assert_eq!(data, [4, 1, 2, 3]);
        assert_eq!(state, NOT_BORROWED);
    }

    #[test]
    fn test_lamports_ref_mut() {
        let mut lamports: u64 = 10000;
        let mut state = 0b_0111_1111;

        let ref_lamports = RefMut {
            value: NonNull::from(&mut lamports),
            borrow_mask: LAMPORTS_MASK,
            // borrow state must be a mutable reference
            state: NonNull::from(&mut state),
            marker: PhantomData,
        };

        let new_ref = RefMut::map(ref_lamports, |lamports| {
            *lamports = 200;
            lamports
        });

        assert_eq!(state, 0b_0111_1111);
        assert_eq!(*new_ref, 200);

        drop(new_ref);

        assert_eq!(lamports, 200);
        assert_eq!(state, NOT_BORROWED);
    }

    #[test]
    fn test_borrow_data() {
        // 8-bytes aligned account data.
        let mut data = [0u64; size_of::<Account>() / size_of::<u64>()];
        // Set the borrow state.
        data[0] = NOT_BORROWED as u64;
        let account_info = AccountInfo {
            raw: data.as_mut_ptr() as *mut Account,
        };

        // Check that we can borrow data and lamports.
        assert!(account_info.can_borrow_data().is_ok());
        assert!(account_info.can_borrow_mut_data().is_ok());
        assert!(account_info.can_borrow_lamports().is_ok());
        assert!(account_info.can_borrow_mut_lamports().is_ok());

        // Borrow immutable data (7 immutable borrows available).
        const ACCOUNT_REF: MaybeUninit<Ref<[u8]>> = MaybeUninit::<Ref<[u8]>>::uninit();
        let mut refs = [ACCOUNT_REF; 7];

        refs.iter_mut().for_each(|r| {
            let Ok(data_ref) = account_info.try_borrow_data() else {
                panic!("Failed to borrow data");
            };
            r.write(data_ref);
        });

        // Check that we cannot borrow the data anymore.
        assert!(account_info.can_borrow_data().is_err());
        assert!(account_info.try_borrow_data().is_err());
        assert!(account_info.can_borrow_mut_data().is_err());
        assert!(account_info.try_borrow_mut_data().is_err());
        // Lamports should still be borrowable.
        assert!(account_info.can_borrow_lamports().is_ok());
        assert!(account_info.can_borrow_mut_lamports().is_ok());

        // Drop the immutable borrows.
        refs.iter_mut().for_each(|r| {
            let r = unsafe { r.assume_init_read() };
            drop(r);
        });

        // We should be able to borrow the data again.
        assert!(account_info.can_borrow_data().is_ok());
        assert!(account_info.can_borrow_mut_data().is_ok());

        // Borrow mutable data.
        let ref_mut = account_info.try_borrow_mut_data().unwrap();

        // Check that we cannot borrow the data anymore.
        assert!(account_info.can_borrow_data().is_err());
        assert!(account_info.try_borrow_data().is_err());
        assert!(account_info.can_borrow_mut_data().is_err());
        assert!(account_info.try_borrow_mut_data().is_err());

        drop(ref_mut);

        // We should be able to borrow the data again.
        assert!(account_info.can_borrow_data().is_ok());
        assert!(account_info.can_borrow_mut_data().is_ok());

        let borrow_state = unsafe { (*account_info.raw).borrow_state };
        assert!(borrow_state == NOT_BORROWED);
    }

    #[test]
    fn test_borrow_lamports() {
        // 8-bytes aligned account data.
        let mut data = [0u64; size_of::<Account>() / size_of::<u64>()];
        // Set the borrow state.
        data[0] = NOT_BORROWED as u64;
        let account_info = AccountInfo {
            raw: data.as_mut_ptr() as *mut Account,
        };

        // Check that we can borrow lamports and data.
        assert!(account_info.can_borrow_lamports().is_ok());
        assert!(account_info.can_borrow_mut_lamports().is_ok());
        assert!(account_info.can_borrow_data().is_ok());
        assert!(account_info.can_borrow_mut_data().is_ok());

        // Borrow immutable lamports (7 immutable borrows available).
        const LAMPORTS_REF: MaybeUninit<Ref<u64>> = MaybeUninit::<Ref<u64>>::uninit();
        let mut refs = [LAMPORTS_REF; 7];

        refs.iter_mut().for_each(|r| {
            let Ok(lamports_ref) = account_info.try_borrow_lamports() else {
                panic!("Failed to borrow lamports");
            };
            r.write(lamports_ref);
        });

        // Check that we cannot borrow the lamports anymore.
        assert!(account_info.can_borrow_lamports().is_err());
        assert!(account_info.try_borrow_lamports().is_err());
        assert!(account_info.can_borrow_mut_lamports().is_err());
        assert!(account_info.try_borrow_mut_lamports().is_err());
        // Data should still be borrowable.
        assert!(account_info.can_borrow_data().is_ok());
        assert!(account_info.can_borrow_mut_data().is_ok());

        // Drop the immutable borrows.
        refs.iter_mut().for_each(|r| {
            let r = unsafe { r.assume_init_read() };
            drop(r);
        });

        // We should be able to borrow the lamports again.
        assert!(account_info.can_borrow_lamports().is_ok());
        assert!(account_info.can_borrow_mut_lamports().is_ok());

        // Borrow mutable lamports.
        let ref_mut = account_info.try_borrow_mut_lamports().unwrap();

        // Check that we cannot borrow the lamports anymore.
        assert!(account_info.can_borrow_lamports().is_err());
        assert!(account_info.try_borrow_lamports().is_err());
        assert!(account_info.can_borrow_mut_lamports().is_err());
        assert!(account_info.try_borrow_mut_lamports().is_err());

        drop(ref_mut);

        // We should be able to borrow the data again.
        assert!(account_info.can_borrow_lamports().is_ok());
        assert!(account_info.can_borrow_mut_lamports().is_ok());

        let borrow_state = unsafe { (*account_info.raw).borrow_state };
        assert!(borrow_state == NOT_BORROWED);
    }

    #[test]
    #[allow(deprecated)]
    fn test_realloc() {
        // 8-bytes aligned account data.
        let mut data = [0u64; 100 * size_of::<u64>()];

        // Set the borrow state.
        data[0] = NOT_BORROWED as u64;
        // Set the initial data length to 100.
        //   - index `10` is equal to offset `10 * size_of::<u64>() = 80` bytes.
        data[10] = 100;

        let account = AccountInfo {
            raw: data.as_mut_ptr() as *const _ as *mut Account,
        };

        assert_eq!(account.data_len(), 100);
        assert_eq!(account.resize_delta(), 0);

        // increase the size.

        account.realloc(200, false).unwrap();

        assert_eq!(account.data_len(), 200);
        assert_eq!(account.resize_delta(), 100);

        // decrease the size.

        account.realloc(0, false).unwrap();

        assert_eq!(account.data_len(), 0);
        assert_eq!(account.resize_delta(), -100);

        // Invalid reallocation.

        let invalid_realloc = account.realloc(10_000_000_001, false);
        assert!(invalid_realloc.is_err());

        // Reset to its original size.

        account.realloc(100, false).unwrap();

        assert_eq!(account.data_len(), 100);
        assert_eq!(account.resize_delta(), 0);

        // Consecutive reallocations.

        account.realloc(200, false).unwrap();
        account.realloc(50, false).unwrap();
        account.realloc(500, false).unwrap();

        assert_eq!(account.data_len(), 500);
        assert_eq!(account.resize_delta(), 400);

        let data = account.try_borrow_data().unwrap();
        assert_eq!(data.len(), 500);
    }
}
