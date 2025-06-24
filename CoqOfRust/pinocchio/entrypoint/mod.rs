//! Macros and functions for defining the program entrypoint and setting up
//! global handlers.

pub mod lazy;
pub use lazy::{InstructionContext, MaybeAccount};

#[cfg(target_os = "solana")]
pub use alloc::BumpAllocator;

use crate::{
    account_info::{Account, AccountInfo, MAX_PERMITTED_DATA_INCREASE},
    pubkey::Pubkey,
    BPF_ALIGN_OF_U128, NON_DUP_MARKER,
};

/// Start address of the memory region used for program heap.
pub const HEAP_START_ADDRESS: u64 = 0x300000000;

/// Length of the heap memory region used for program heap.
pub const HEAP_LENGTH: usize = 32 * 1024;

#[deprecated(
    since = "0.6.0",
    note = "Use `ProgramResult` from the crate root instead"
)]
/// The result of a program execution.
pub type ProgramResult = super::ProgramResult;

#[deprecated(since = "0.6.0", note = "Use `SUCCESS` from the crate root instead")]
/// Return value for a successful program execution.
pub const SUCCESS: u64 = super::SUCCESS;

/// The "static" size of an account in the input buffer.
///
/// This is the size of the account header plus the maximum permitted data increase.
const STATIC_ACCOUNT_DATA: usize = core::mem::size_of::<Account>() + MAX_PERMITTED_DATA_INCREASE;

/// Declare the program entrypoint and set up global handlers.
///
/// The main difference from the standard (SDK) [`entrypoint`](https://docs.rs/solana-program-entrypoint/latest/solana_program_entrypoint/macro.entrypoint.html)
/// macro is that this macro represents an entrypoint that does not perform allocations or copies
/// when reading the input buffer.
///
/// This macro emits the common boilerplate necessary to begin program execution, calling a
/// provided function to process the program instruction supplied by the runtime, and reporting
/// its result to the runtime.
///
/// It also sets up a [global allocator] and [panic handler], using the [`crate::default_allocator!`]
/// and [`crate::default_panic_handler!`] macros.
///
/// The first argument is the name of a function with this type signature:
///
/// ```ignore
/// fn process_instruction(
///     program_id: &Pubkey,      // Public key of the account the program was loaded into
///     accounts: &[AccountInfo], // All accounts required to process the instruction
///     instruction_data: &[u8],  // Serialized instruction-specific data
/// ) -> ProgramResult;
/// ```
/// The argument is defined as an `expr`, which allows the use of any function pointer not just
/// identifiers in the current scope.
///
/// There is a second optional argument that allows to specify the maximum number of accounts
/// expected by instructions of the program. This is useful to reduce the stack size requirement
/// for the entrypoint, as the default is set to [`crate::MAX_TX_ACCOUNTS`]. If the program
/// receives more accounts than the specified maximum, these accounts will be ignored.
///
/// [global allocator]: https://doc.rust-lang.org/stable/alloc/alloc/trait.GlobalAlloc.html
/// [maximum number of accounts]: https://github.com/anza-xyz/agave/blob/ccabfcf84921977202fd06d3197cbcea83742133/runtime/src/bank.rs#L3207-L3219
/// [panic handler]: https://doc.rust-lang.org/stable/core/panic/trait.PanicHandler.html
///
/// # Examples
///
/// Defining an entrypoint conditional on the `bpf-entrypoint` feature. Although the `entrypoint`
/// module is written inline in this example, it is common to put it into its own file.
///
/// ```no_run
/// #[cfg(feature = "bpf-entrypoint")]
/// pub mod entrypoint {
///
///     use pinocchio::{
///         account_info::AccountInfo,
///         entrypoint,
///         msg,
///         pubkey::Pubkey,
///         ProgramResult
///     };
///
///     entrypoint!(process_instruction);
///
///     pub fn process_instruction(
///         program_id: &Pubkey,
///         accounts: &[AccountInfo],
///         instruction_data: &[u8],
///     ) -> ProgramResult {
///         msg!("Hello from my program!");
///         Ok(())
///     }
///
/// }
/// ```
///
/// # Important
///
/// The panic handler set up is different depending on whether the `std` library is available to the
/// linker or not. The `entrypoint` macro will set up a default
/// panic "hook", that works with the `#[panic_handler]` set by the `std`. Therefore, this macro
/// should be used when the program or any of its dependencies are dependent on the `std` library.
///
/// When the program and all its dependencies are `no_std`, it is necessary to set a
/// `#[panic_handler]` to handle panics. This is done by the [`crate::nostd_panic_handler`](https://docs.rs/pinocchio/latest/pinocchio/macro.nostd_panic_handler.html)
/// macro. In this case, it is not possible to use the `entrypoint`
/// macro. Use the [`crate::program_entrypoint!`] macro instead and set up the allocator and panic
/// handler manually.
#[macro_export]
macro_rules! entrypoint {
    ( $process_instruction:expr ) => {
        $crate::program_entrypoint!($process_instruction);
        $crate::default_allocator!();
        $crate::default_panic_handler!();
    };
    ( $process_instruction:expr, $maximum:expr ) => {
        $crate::program_entrypoint!($process_instruction, $maximum);
        $crate::default_allocator!();
        $crate::default_panic_handler!();
    };
}

/// Declare the program entrypoint.
///
/// This macro is similar to the [`crate::entrypoint!`] macro, but it does
/// not set up a global allocator nor a panic handler. This is useful when the program will set up
/// its own allocator and panic handler.
///
/// The first argument is the name of a function with this type signature:
///
/// ```ignore
/// fn process_instruction(
///     program_id: &Pubkey,      // Public key of the account the program was loaded into
///     accounts: &[AccountInfo], // All accounts required to process the instruction
///     instruction_data: &[u8],  // Serialized instruction-specific data
/// ) -> ProgramResult;
/// ```
/// The argument is defined as an `expr`, which allows the use of any function pointer not just
/// identifiers in the current scope.
///
/// There is a second optional argument that allows to specify the maximum number of accounts
/// expected by instructions of the program. This is useful to reduce the stack size requirement
/// for the entrypoint, as the default is set to [`crate::MAX_TX_ACCOUNTS`]. If the program
/// receives more accounts than the specified maximum, these accounts will be ignored.
#[macro_export]
macro_rules! program_entrypoint {
    ( $process_instruction:expr ) => {
        /// Program entrypoint.
        #[no_mangle]
        pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
            const UNINIT: core::mem::MaybeUninit<$crate::account_info::AccountInfo> =
                core::mem::MaybeUninit::<$crate::account_info::AccountInfo>::uninit();
            // Create an array of uninitialized account infos.
            let mut accounts = [UNINIT; { $crate::MAX_TX_ACCOUNTS }];

            let (program_id, count, instruction_data) =
                $crate::entrypoint::parse(input, &mut accounts);

            // Call the program's entrypoint passing `count` account infos; we know that
            // they are initialized so we cast the pointer to a slice of `[AccountInfo]`.
            match $process_instruction(
                &program_id,
                core::slice::from_raw_parts(accounts.as_ptr() as _, count),
                &instruction_data,
            ) {
                Ok(()) => $crate::SUCCESS,
                Err(error) => error.into(),
            }
        }
    };
    ( $process_instruction:expr, $maximum:expr ) => {
        /// Program entrypoint.
        #[no_mangle]
        pub unsafe extern "C" fn entrypoint(input: *mut u8) -> u64 {
            const UNINIT: core::mem::MaybeUninit<$crate::account_info::AccountInfo> =
                core::mem::MaybeUninit::<$crate::account_info::AccountInfo>::uninit();
            // Create an array of uninitialized account infos.
            let mut accounts = [UNINIT; $maximum];

            let (program_id, count, instruction_data) =
                $crate::entrypoint::deserialize::<$maximum>(input, &mut accounts);

            // Call the program's entrypoint passing `count` account infos; we know that
            // they are initialized so we cast the pointer to a slice of `[AccountInfo]`.
            match $process_instruction(
                &program_id,
                core::slice::from_raw_parts(accounts.as_ptr() as _, count),
                &instruction_data,
            ) {
                Ok(()) => $crate::SUCCESS,
                Err(error) => error.into(),
            }
        }
    };
}

/// Parse the input arguments from the runtime input buffer.
///
/// Note that this function will only parse up to `MAX_ACCOUNTS` accounts; any
/// additional accounts will be ignored.
///
/// This can only be called from the entrypoint function of a Solana program and with
/// a buffer that was serialized by the runtime.
///
/// # Safety
///
/// The caller must ensure that the input buffer is valid, i.e., it represents the
/// program input parameters serialized by the SVM loader.
#[allow(clippy::cast_ptr_alignment)]
#[inline(always)]
pub unsafe fn deserialize<'a, const MAX_ACCOUNTS: usize>(
    mut input: *mut u8,
    accounts: &mut [core::mem::MaybeUninit<AccountInfo>; MAX_ACCOUNTS],
) -> (&'a Pubkey, usize, &'a [u8]) {
    // Total number of accounts present in the input buffer.
    let mut processed = *(input as *const u64) as usize;
    input = input.add(core::mem::size_of::<u64>());

    if processed > 0 {
        let total_accounts = processed;
        // Number of accounts to process (limited to MAX_ACCOUNTS).
        processed = core::cmp::min(total_accounts, MAX_ACCOUNTS);

        for i in 0..processed {
            let account_info: *mut Account = input as *mut Account;
            // Adds an 8-bytes offset for:
            //   - rent epoch in case of a non-duplicated account
            //   - duplicated marker + 7 bytes of padding in case of a duplicated account
            input = input.add(core::mem::size_of::<u64>());

            let account = if (*account_info).borrow_state == NON_DUP_MARKER {
                // Unique account: create a new `AccountInfo` to represent the account.
                input = input.add(STATIC_ACCOUNT_DATA);
                input = input.add((*account_info).data_len as usize);
                input = input.add(input.align_offset(BPF_ALIGN_OF_U128));

                AccountInfo { raw: account_info }
            } else {
                // Duplicated account: clone the original pointer using `borrow_state` since
                // it represents the index of the duplicated account passed by the runtime.
                accounts
                    .get_unchecked((*account_info).borrow_state as usize)
                    .assume_init_ref()
                    .clone()
            };

            accounts.get_unchecked_mut(i).write(account);
        }

        // Process any remaining accounts to move the offset to the instruction
        // data (there is a duplication of logic but we avoid testing whether we
        // have space for the account or not).
        for _ in processed..total_accounts {
            let account_info: *mut Account = input as *mut Account;
            // Adds an 8-bytes offset for:
            //   - rent epoch in case of a non-duplicate account
            //   - duplicate marker + 7 bytes of padding in case of a duplicate account
            input = input.add(core::mem::size_of::<u64>());

            if (*account_info).borrow_state == NON_DUP_MARKER {
                input = input.add(STATIC_ACCOUNT_DATA);
                input = input.add((*account_info).data_len as usize);
                input = input.add(input.align_offset(BPF_ALIGN_OF_U128));
            }
        }
    }

    // instruction data
    let instruction_data_len = *(input as *const u64) as usize;
    input = input.add(core::mem::size_of::<u64>());

    let instruction_data = { core::slice::from_raw_parts(input, instruction_data_len) };
    input = input.add(instruction_data_len);

    // program id
    let program_id: &Pubkey = &*(input as *const Pubkey);

    (program_id, processed, instruction_data)
}

/// Parse the input arguments from the runtime input buffer.
///
/// This can only be called from the entrypoint function of a Solana program with
/// a buffer serialized by the runtime.
///
/// # Safety
///
/// The caller must ensure that the `input` buffer is valid, i.e., it represents the
/// program input parameters serialized by the SVM loader. Additionally, the `input`
/// should last for the lifetime of the program execution since the returnerd values
/// reference the `input`.
#[inline(always)]
pub unsafe fn parse<const ACCOUNTS: usize>(
    mut input: *mut u8,
    accounts: &mut [core::mem::MaybeUninit<AccountInfo>; ACCOUNTS],
) -> (&'static Pubkey, usize, &'static [u8]) {
    // Ensure that the number of accounts is equal to `MAX_TX_ACCOUNTS`.
    const {
        assert!(
            ACCOUNTS == crate::MAX_TX_ACCOUNTS,
            "The number of accounts must be equal to MAX_TX_ACCOUNTS"
        );
    }
    // The runtime guarantees that the number of accounts does not exceed
    // `MAX_TX_ACCOUNTS`.
    let processed = *(input as *const u64) as usize;
    input = input.add(core::mem::size_of::<u64>());

    for i in 0..processed {
        let account_info: *mut Account = input as *mut Account;
        // Adds an 8-bytes offset for:
        //   - rent epoch in case of a non-duplicated account
        //   - duplicated marker + 7 bytes of padding in case of a duplicated account
        input = input.add(core::mem::size_of::<u64>());

        let account = if (*account_info).borrow_state == NON_DUP_MARKER {
            // Unique account: create a new `AccountInfo` to represent the account.
            input = input.add(STATIC_ACCOUNT_DATA);
            input = input.add((*account_info).data_len as usize);
            input = input.add(input.align_offset(BPF_ALIGN_OF_U128));

            AccountInfo { raw: account_info }
        } else {
            // Duplicated account: clone the original pointer using `borrow_state` since
            // it represents the index of the duplicated account passed by the runtime.
            accounts
                .get_unchecked((*account_info).borrow_state as usize)
                .assume_init_ref()
                .clone()
        };

        accounts.get_unchecked_mut(i).write(account);
    }

    // instruction data
    let instruction_data_len = *(input as *const u64) as usize;
    input = input.add(core::mem::size_of::<u64>());

    let instruction_data = { core::slice::from_raw_parts(input, instruction_data_len) };
    input = input.add(instruction_data_len);

    // program id
    let program_id: &Pubkey = &*(input as *const Pubkey);

    (program_id, processed, instruction_data)
}

/// Default panic hook.
///
/// This macro sets up a default panic hook that logs the panic message and the file where the
/// panic occurred. It acts as a hook after Rust runtime panics; syscall `abort()` will be called
/// after it returns.
///
/// Note that this requires the `"std"` feature to be enabled.
#[cfg(feature = "std")]
#[macro_export]
macro_rules! default_panic_handler {
    () => {
        /// Default panic handler.
        #[cfg(target_os = "solana")]
        #[no_mangle]
        fn custom_panic(info: &core::panic::PanicInfo<'_>) {
            // Panic reporting.
            $crate::msg!("{}", info);
        }
    };
}

/// Default panic hook.
///
/// This macro sets up a default panic hook that logs the file where the panic occurred. It acts
/// as a hook after Rust runtime panics; syscall `abort()` will be called after it returns.
///
/// This is used when the `"std"` feature is disabled, while either the program or any of its
/// dependencies are not `no_std`.
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! default_panic_handler {
    () => {
        /// Default panic handler.
        #[cfg(target_os = "solana")]
        #[no_mangle]
        fn custom_panic(info: &core::panic::PanicInfo<'_>) {
            if let Some(location) = info.location() {
                $crate::log::sol_log(location.file());
            }
            // Panic reporting.
            $crate::log::sol_log("** PANICKED **");
        }
    };
}

/// A global `#[panic_handler]` for `no_std` programs.
///
/// This macro sets up a default panic handler that logs the location (file, line and column)
/// where the panic occurred and then calls the syscall `abort()`.
///
/// This macro can only be used when all crates are `no_std` and the `"std"` feature is
/// disabled.
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! nostd_panic_handler {
    () => {
        /// A panic handler for `no_std`.
        #[cfg(target_os = "solana")]
        #[no_mangle]
        #[panic_handler]
        fn handler(info: &core::panic::PanicInfo<'_>) -> ! {
            if let Some(location) = info.location() {
                unsafe {
                    $crate::syscalls::sol_panic_(
                        location.file().as_ptr(),
                        location.file().len() as u64,
                        location.line() as u64,
                        location.column() as u64,
                    )
                }
            } else {
                // Panic reporting.
                $crate::log::sol_log("** PANICKED **");
                unsafe { $crate::syscalls::abort() }
            }
        }

        /// A panic handler for when the program is compiled on a target different than
        /// `"solana"`.
        ///
        /// This links the `std` library, which will set up a default panic handler.
        #[cfg(not(target_os = "solana"))]
        mod __private_panic_handler {
            extern crate std as __std;
        }
    };
}

/// Default global allocator.
///
/// This macro sets up a default global allocator that uses a bump allocator to allocate memory.
#[macro_export]
macro_rules! default_allocator {
    () => {
        #[cfg(target_os = "solana")]
        #[global_allocator]
        static A: $crate::entrypoint::BumpAllocator = $crate::entrypoint::BumpAllocator {
            start: $crate::entrypoint::HEAP_START_ADDRESS as usize,
            len: $crate::entrypoint::HEAP_LENGTH,
        };

        /// A default allocator for when the program is compiled on a target different than
        /// `"solana"`.
        ///
        /// This links the `std` library, which will set up a default global allocator.
        #[cfg(not(target_os = "solana"))]
        mod __private_alloc {
            extern crate std as __std;
        }
    };
}

/// A global allocator that does not allocate memory.
///
/// Using this macro with the "`std`" feature enabled will result in a compile error.
#[cfg(feature = "std")]
#[macro_export]
macro_rules! no_allocator {
    () => {
        compile_error!("Feature 'std' cannot be enabled.");
    };
}

/// A global allocator that does not dynamically allocate memory.
///
/// This macro sets up a global allocator that denies all dynamic allocations, while
/// allowing static ("manual") allocations. This is useful when the program does not need to
/// dynamically allocate memory and manages their own allocations.
///
/// The program will panic if it tries to dynamically allocate memory.
///
/// This is used when the `"std"` feature is disabled.
#[cfg(not(feature = "std"))]
#[macro_export]
macro_rules! no_allocator {
    () => {
        #[cfg(target_os = "solana")]
        #[global_allocator]
        static A: $crate::entrypoint::NoAllocator = $crate::entrypoint::NoAllocator;

        /// Allocates memory for the given type `T` at the specified offset in the
        /// heap reserved address space.
        ///
        /// # Safety
        ///
        /// It is the caller's responsibility to ensure that the offset does not
        /// overlap with previous allocations and that type `T` can hold the bit-pattern
        /// `0` as a valid value.
        ///
        /// For types that cannot hold the bit-pattern `0` as a valid value, use
        /// `core::mem::MaybeUninit<T>` to allocate memory for the type and
        /// initialize it later.
        //
        // Make this `const` once `const_mut_refs` is stable for the platform-tools
        // toolchain Rust version.
        #[inline(always)]
        pub unsafe fn allocate_unchecked<T: Sized>(offset: usize) -> &'static mut T {
            // SAFETY: The pointer is within a valid range and aligned to `T`.
            unsafe { &mut *(calculate_offset::<T>(offset) as *mut T) }
        }

        #[inline(always)]
        const fn calculate_offset<T: Sized>(offset: usize) -> usize {
            let start = $crate::entrypoint::HEAP_START_ADDRESS as usize + offset;
            let end = start + core::mem::size_of::<T>();

            // Assert if the allocation does not exceed the heap size.
            assert!(
                end <= $crate::entrypoint::HEAP_START_ADDRESS as usize
                    + $crate::entrypoint::HEAP_LENGTH,
                "allocation exceeds heap size"
            );

            // Assert if the pointer is aligned to `T`.
            assert!(
                start % core::mem::align_of::<T>() == 0,
                "offset is not aligned"
            );

            start
        }

        /// A default allocator for when the program is compiled on a target different than
        /// `"solana"`.
        ///
        /// This links the `std` library, which will set up a default global allocator.
        #[cfg(not(target_os = "solana"))]
        mod __private_alloc {
            extern crate std as __std;
        }
    };
}

#[cfg(target_os = "solana")]
mod alloc {
    //! The bump allocator used as the default rust heap when running programs.

    extern crate alloc;

    /// The bump allocator used as the default rust heap when running programs.
    pub struct BumpAllocator {
        pub start: usize,
        pub len: usize,
    }

    /// Integer arithmetic in this global allocator implementation is safe when
    /// operating on the prescribed [`HEAP_START_ADDRESS`] and [`HEAP_LENGTH`]. Any
    /// other use may overflow and is thus unsupported and at one's own risk.
    #[allow(clippy::arithmetic_side_effects)]
    unsafe impl alloc::alloc::GlobalAlloc for BumpAllocator {
        /// Allocates memory as a bump allocator.
        #[inline]
        unsafe fn alloc(&self, layout: core::alloc::Layout) -> *mut u8 {
            let pos_ptr = self.start as *mut usize;

            let mut pos = *pos_ptr;
            if pos == 0 {
                // First time, set starting position.
                pos = self.start + self.len;
            }
            pos = pos.saturating_sub(layout.size());
            pos &= !(layout.align().wrapping_sub(1));
            if pos < self.start + core::mem::size_of::<*mut u8>() {
                return core::ptr::null_mut();
            }
            *pos_ptr = pos;
            pos as *mut u8
        }
        #[inline]
        unsafe fn dealloc(&self, _: *mut u8, _: core::alloc::Layout) {
            // I'm a bump allocator, I don't free.
        }
    }
}

#[cfg(not(feature = "std"))]
/// An allocator that does not allocate memory.
pub struct NoAllocator;

#[cfg(not(feature = "std"))]
unsafe impl core::alloc::GlobalAlloc for NoAllocator {
    #[inline]
    unsafe fn alloc(&self, _: core::alloc::Layout) -> *mut u8 {
        panic!("** NO ALLOCATOR **");
    }

    #[inline]
    unsafe fn dealloc(&self, _: *mut u8, _: core::alloc::Layout) {
        // I deny all allocations, so I don't need to free.
    }
}
