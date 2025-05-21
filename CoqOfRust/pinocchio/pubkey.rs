//! Public key type and functions.

use crate::program_error::ProgramError;

/// Number of bytes in a pubkey.
pub const PUBKEY_BYTES: usize = 32;

/// maximum length of derived `Pubkey` seed.
pub const MAX_SEED_LEN: usize = 32;

/// Maximum number of seeds.
pub const MAX_SEEDS: usize = 16;

/// The address of a [Solana account][account].
///
/// [account]: https://solana.com/docs/core/accounts
pub type Pubkey = [u8; PUBKEY_BYTES];

/// Log a `Pubkey` from a program.
#[inline(always)]
pub fn log(pubkey: &Pubkey) {
    #[cfg(target_os = "solana")]
    unsafe {
        crate::syscalls::sol_log_pubkey(pubkey as *const _ as *const u8)
    };

    #[cfg(not(target_os = "solana"))]
    core::hint::black_box(pubkey);
}

/// Find a valid [program derived address][pda] and its corresponding bump seed.
///
/// [pda]: https://solana.com/docs/core/cpi#program-derived-addresses
///
/// Program derived addresses (PDAs) are account keys that only the program,
/// `program_id`, has the authority to sign. The address is of the same form
/// as a Solana `Pubkey`, except they are ensured to not be on the ed25519
/// curve and thus have no associated private key. When performing
/// cross-program invocations the program can "sign" for the key by calling
/// [`invoke_signed`] and passing the same seeds used to generate the
/// address, along with the calculated _bump seed_, which this function
/// returns as the second tuple element. The runtime will verify that the
/// program associated with this address is the caller and thus authorized
/// to be the signer.
///
/// [`invoke_signed`]: crate::program::invoke_signed
///
/// The `seeds` are application-specific, and must be carefully selected to
/// uniquely derive accounts per application requirements. It is common to
/// use static strings and other pubkeys as seeds.
///
/// Because the program address must not lie on the ed25519 curve, there may
/// be seed and program id combinations that are invalid. For this reason,
/// an extra seed (the bump seed) is calculated that results in a
/// point off the curve. The bump seed must be passed as an additional seed
/// when calling `invoke_signed`.
///
/// The processes of finding a valid program address is by trial and error,
/// and even though it is deterministic given a set of inputs it can take a
/// variable amount of time to succeed across different inputs.  This means
/// that when called from an on-chain program it may incur a variable amount
/// of the program's compute budget.  Programs that are meant to be very
/// performant may not want to use this function because it could take a
/// considerable amount of time. Programs that are already at risk
/// of exceeding their compute budget should call this with care since
/// there is a chance that the program's budget may be occasionally
/// and unpredictably exceeded.
///
/// As all account addresses accessed by an on-chain Solana program must be
/// explicitly passed to the program, it is typical for the PDAs to be
/// derived in off-chain client programs, avoiding the compute cost of
/// generating the address on-chain. The address may or may not then be
/// verified by re-deriving it on-chain, depending on the requirements of
/// the program. This verification may be performed without the overhead of
/// re-searching for the bump key by using the [`create_program_address`]
/// function.
///
/// [`create_program_address`]: crate::pubkey::create_program_address
///
/// **Warning**: Because of the way the seeds are hashed there is a potential
/// for program address collisions for the same program id.  The seeds are
/// hashed sequentially which means that seeds {"abcdef"}, {"abc", "def"},
/// and {"ab", "cd", "ef"} will all result in the same program address given
/// the same program id. Since the chance of collision is local to a given
/// program id, the developer of that program must take care to choose seeds
/// that do not collide with each other. For seed schemes that are susceptible
/// to this type of hash collision, a common remedy is to insert separators
/// between seeds, e.g. transforming {"abc", "def"} into {"abc", "-", "def"}.
///
/// # Panics
///
/// Panics in the statistically improbable event that a bump seed could not be
/// found. Use [`try_find_program_address`] to handle this case.
///
/// [`try_find_program_address`]: #try_find_program_address
///
/// Panics if any of the following are true:
///
/// - the number of provided seeds is greater than, _or equal to_, [`MAX_SEEDS`],
/// - any individual seed's length is greater than [`MAX_SEED_LEN`].
#[inline(always)]
pub fn find_program_address(seeds: &[&[u8]], program_id: &Pubkey) -> (Pubkey, u8) {
    try_find_program_address(seeds, program_id)
        .unwrap_or_else(|| panic!("Unable to find a viable program address bump seed"))
}

/// Find a valid [program derived address][pda] and its corresponding bump seed.
///
/// [pda]: https://solana.com/docs/core/cpi#program-derived-addresses
///
/// The only difference between this method and [`find_program_address`]
/// is that this one returns `None` in the statistically improbable event
/// that a bump seed cannot be found; or if any of `find_program_address`'s
/// preconditions are violated.
///
/// See the documentation for [`find_program_address`] for a full description.
///
/// [`find_program_address`]: #find_program_address
#[inline]
pub fn try_find_program_address(seeds: &[&[u8]], program_id: &Pubkey) -> Option<(Pubkey, u8)> {
    #[cfg(target_os = "solana")]
    {
        let mut bytes = core::mem::MaybeUninit::<[u8; PUBKEY_BYTES]>::uninit();
        let mut bump_seed = u8::MAX;

        let result = unsafe {
            crate::syscalls::sol_try_find_program_address(
                seeds as *const _ as *const u8,
                seeds.len() as u64,
                program_id as *const _,
                bytes.as_mut_ptr() as *mut _,
                &mut bump_seed as *mut _,
            )
        };
        match result {
            // SAFETY: The syscall has initialized the bytes.
            crate::SUCCESS => Some((unsafe { bytes.assume_init() }, bump_seed)),
            _ => None,
        }
    }

    #[cfg(not(target_os = "solana"))]
    {
        core::hint::black_box((seeds, program_id));
        None
    }
}

/// Create a valid [program derived address][pda] without searching for a bump seed.
///
/// [pda]: https://solana.com/docs/core/cpi#program-derived-addresses
///
/// Because this function does not create a bump seed, it may unpredictably
/// return an error for any given set of seeds and is not generally suitable
/// for creating program derived addresses.
///
/// However, it can be used for efficiently verifying that a set of seeds plus
/// bump seed generated by [`find_program_address`] derives a particular
/// address as expected. See the example for details.
///
/// See the documentation for [`find_program_address`] for a full description
/// of program derived addresses and bump seeds.
///
/// Note that this function does *not* validate whether the given `seeds` are within
/// the valid length or not. It will return an error in case of invalid seeds length,
/// incurring the cost of the syscall.
///
/// [`find_program_address`]: #find_program_address
#[inline]
pub fn create_program_address(
    seeds: &[&[u8]],
    program_id: &Pubkey,
) -> Result<Pubkey, ProgramError> {
    // Call via a system call to perform the calculation
    #[cfg(target_os = "solana")]
    {
        let mut bytes = core::mem::MaybeUninit::<[u8; PUBKEY_BYTES]>::uninit();

        let result = unsafe {
            crate::syscalls::sol_create_program_address(
                seeds as *const _ as *const u8,
                seeds.len() as u64,
                program_id as *const _ as *const u8,
                bytes.as_mut_ptr() as *mut u8,
            )
        };

        match result {
            // SAFETY: The syscall has initialized the bytes.
            crate::SUCCESS => Ok(unsafe { bytes.assume_init() }),
            _ => Err(result.into()),
        }
    }

    #[cfg(not(target_os = "solana"))]
    {
        core::hint::black_box((seeds, program_id));
        panic!("create_program_address is only available on target `solana`")
    }
}

/// Create a valid [program derived address][pda] without searching for a bump seed.
///
/// [pda]: https://solana.com/docs/core/cpi#program-derived-addresses
///
/// Because this function does not create a bump seed, it may unpredictably
/// return an error for any given set of seeds and is not generally suitable
/// for creating program derived addresses.
///
/// However, it can be used for efficiently verifying that a set of seeds plus
/// bump seed generated by [`find_program_address`] derives a particular
/// address as expected. See the example for details.
///
/// See the documentation for [`find_program_address`] for a full description
/// of program derived addresses and bump seeds.
///
/// Note that this function validates whether the given `seeds` are within the valid
/// length or not, returning an error without incurring the cost of the syscall.
///
/// [`find_program_address`]: #find_program_address
#[inline(always)]
pub fn checked_create_program_address(
    seeds: &[&[u8]],
    program_id: &Pubkey,
) -> Result<Pubkey, ProgramError> {
    if seeds.len() > MAX_SEEDS {
        return Err(ProgramError::MaxSeedLengthExceeded);
    }
    if seeds.iter().any(|seed| seed.len() > MAX_SEED_LEN) {
        return Err(ProgramError::MaxSeedLengthExceeded);
    }

    create_program_address(seeds, program_id)
}
