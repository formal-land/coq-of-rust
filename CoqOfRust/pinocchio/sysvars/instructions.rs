use crate::{
    account_info::{AccountInfo, Ref},
    instruction::AccountMeta,
    program_error::ProgramError,
    pubkey::{Pubkey, PUBKEY_BYTES},
};

use core::{marker::PhantomData, mem::size_of, ops::Deref};

/// Sysvar1nstructions1111111111111111111111111
pub const INSTRUCTIONS_ID: Pubkey = [
    0x06, 0xa7, 0xd5, 0x17, 0x18, 0x7b, 0xd1, 0x66, 0x35, 0xda, 0xd4, 0x04, 0x55, 0xfd, 0xc2, 0xc0,
    0xc1, 0x24, 0xc6, 0x8f, 0x21, 0x56, 0x75, 0xa5, 0xdb, 0xba, 0xcb, 0x5f, 0x08, 0x00, 0x00, 0x00,
];

pub struct Instructions<T>
where
    T: Deref<Target = [u8]>,
{
    data: T,
}

impl<T> Instructions<T>
where
    T: Deref<Target = [u8]>,
{
    /// Creates a new `Instructions` struct.
    ///
    /// `data` is the instructions sysvar account data.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check if the provided data is from the Sysvar Account.
    #[inline(always)]
    pub unsafe fn new_unchecked(data: T) -> Self {
        Instructions { data }
    }

    /// Load the current `Instruction`'s index in the currently executing
    /// `Transaction`.
    #[inline(always)]
    pub fn load_current_index(&self) -> u16 {
        let len = self.data.len();
        // SAFETY: The last 2 bytes of the Instructions sysvar data represents the current
        // instruction index.
        unsafe { u16::from_le_bytes(*(self.data.as_ptr().add(len - 2) as *const [u8; 2])) }
    }

    /// Creates and returns an `IntrospectedInstruction` for the instruction at the specified index.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not check if the provided index is out of bounds. It is
    /// typically used internally with the `load_instruction_at` or `get_instruction_relative` functions,
    /// which perform the necessary index verification.
    #[inline(always)]
    pub unsafe fn deserialize_instruction_unchecked(
        &self,
        index: usize,
    ) -> IntrospectedInstruction {
        let offset = *(self
            .data
            .as_ptr()
            .add(size_of::<u16>() + index * size_of::<u16>()) as *const u16);

        IntrospectedInstruction {
            raw: self.data.as_ptr().add(offset as usize),
            marker: PhantomData,
        }
    }

    /// Creates and returns an `IntrospectedInstruction` for the instruction at the specified index.
    #[inline(always)]
    pub fn load_instruction_at(
        &self,
        index: usize,
    ) -> Result<IntrospectedInstruction, ProgramError> {
        // SAFETY: The first 2 bytes of the Instructions sysvar data represents the
        // number of instructions.
        let num_instructions = unsafe { *(self.data.as_ptr() as *const u16) };

        if index >= num_instructions as usize {
            return Err(ProgramError::InvalidInstructionData);
        }

        // SAFETY: The index was checked to be in bounds.
        Ok(unsafe { self.deserialize_instruction_unchecked(index) })
    }

    /// Creates and returns an `IntrospectedInstruction` relative to the current `Instruction` in the
    /// currently executing `Transaction.
    #[inline(always)]
    pub fn get_instruction_relative(
        &self,
        index_relative_to_current: i64,
    ) -> Result<IntrospectedInstruction, ProgramError> {
        let current_index = self.load_current_index() as i64;
        let index = current_index.saturating_add(index_relative_to_current);

        if index < 0 {
            return Err(ProgramError::InvalidInstructionData);
        }

        self.load_instruction_at(index as usize)
    }
}

impl<'a> TryFrom<&'a AccountInfo> for Instructions<Ref<'a, [u8]>> {
    type Error = ProgramError;

    #[inline(always)]
    fn try_from(account_info: &'a AccountInfo) -> Result<Self, Self::Error> {
        if account_info.key() != &INSTRUCTIONS_ID {
            return Err(ProgramError::UnsupportedSysvar);
        }

        Ok(Instructions {
            data: account_info.try_borrow_data()?,
        })
    }
}

#[repr(C)]
#[derive(Clone, PartialEq, Eq)]
pub struct IntrospectedInstruction<'a> {
    pub raw: *const u8,
    pub marker: PhantomData<&'a [u8]>,
}

impl IntrospectedInstruction<'_> {
    /// Get the account meta at the specified index.
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not verify if the index is out of bounds.
    ///
    /// It is typically used internally within the `get_account_meta_at` function, which
    /// performs the necessary index verification. However, to optimize performance for users
    /// who are sure that the index is in bounds, we have exposed it as an unsafe function.
    #[inline(always)]
    pub unsafe fn get_account_meta_at_unchecked(&self, index: usize) -> &IntrospectedAccountMeta {
        let offset = core::mem::size_of::<u16>() + (index * IntrospectedAccountMeta::LEN);
        &*(self.raw.add(offset) as *const IntrospectedAccountMeta)
    }

    /// Get the account meta at the specified index.
    ///
    /// # Errors
    ///
    /// Returns [`ProgramError::InvalidArgument`] if the index is out of bounds.
    #[inline(always)]
    pub fn get_account_meta_at(
        &self,
        index: usize,
    ) -> Result<&IntrospectedAccountMeta, ProgramError> {
        // SAFETY: The first 2 bytes represent the number of accounts in the instruction.
        let num_accounts = u16::from_le_bytes(unsafe { *(self.raw as *const [u8; 2]) });

        if index >= num_accounts as usize {
            return Err(ProgramError::InvalidArgument);
        }

        // SAFETY: The index was checked to be in bounds.
        Ok(unsafe { self.get_account_meta_at_unchecked(index) })
    }

    /// Get the program ID of the `Instruction`.
    #[inline(always)]
    pub fn get_program_id(&self) -> &Pubkey {
        // SAFETY: The first 2 bytes represent the number of accounts in the instruction.
        let num_accounts = u16::from_le_bytes(unsafe { *(self.raw as *const [u8; 2]) });

        // SAFETY: The program ID is located after the account metas.
        unsafe {
            &*(self.raw.add(
                size_of::<u16>() + num_accounts as usize * size_of::<IntrospectedAccountMeta>(),
            ) as *const Pubkey)
        }
    }

    /// Get the instruction data of the `Instruction`.
    #[inline(always)]
    pub fn get_instruction_data(&self) -> &[u8] {
        // SAFETY: The first 2 bytes represent the number of accounts in the instruction.
        let offset = u16::from_le_bytes(unsafe { *(self.raw as *const [u8; 2]) }) as usize
            * size_of::<IntrospectedAccountMeta>()
            + PUBKEY_BYTES;

        // SAFETY: The instruction data length is located after the program ID.
        let data_len = u16::from_le_bytes(unsafe {
            *(self.raw.add(size_of::<u16>() + offset) as *const [u8; 2])
        });

        // SAFETY: The instruction data is located after the data length.
        unsafe {
            core::slice::from_raw_parts(
                self.raw.add(size_of::<u16>() + offset + size_of::<u16>()),
                data_len as usize,
            )
        }
    }
}

/// The bit positions for the signer flags in the `AccountMeta`.
const IS_SIGNER: u8 = 0b00000001;

/// The bit positions for the writable flags in the `AccountMeta`.
const IS_WRITABLE: u8 = 0b00000010;

#[repr(C)]
#[derive(Clone, PartialEq, Eq)]
pub struct IntrospectedAccountMeta {
    /// Account flags:
    ///   * bit `0`: signer
    ///   * bit `1`: writable
    flags: u8,

    /// The account key.
    pub key: Pubkey,
}

impl IntrospectedAccountMeta {
    const LEN: usize = core::mem::size_of::<Self>();

    /// Indicate whether the account is writable or not.
    #[inline(always)]
    pub fn is_writable(&self) -> bool {
        (self.flags & IS_WRITABLE) != 0
    }

    /// Indicate whether the account is a signer or not.
    #[inline(always)]
    pub fn is_signer(&self) -> bool {
        (self.flags & IS_SIGNER) != 0
    }

    /// Convert the `IntrospectedAccountMeta` to an `AccountMeta`.
    #[inline(always)]
    pub fn to_account_meta(&self) -> AccountMeta {
        AccountMeta::new(&self.key, self.is_writable(), self.is_signer())
    }
}
