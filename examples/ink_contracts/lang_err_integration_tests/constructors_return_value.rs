#[derive(Default, Clone, Copy)]
struct AccountId(u128);

impl From<[u8; 32]> for AccountId {
    fn from(_value: [u8; 32]) -> Self {
        unimplemented!()
    }
}

type Balance = u128;

pub struct ConstructorsReturnValue {
    value: bool,
}

pub enum LangError {
    CouldNotReadInput,
}

pub type ConstructorResult<T> = Result<T, LangError>;

#[derive(Debug)]
#[cfg_attr(feature = "std", derive(scale_info::TypeInfo))]
pub struct ConstructorError;

pub struct ReturnFlags {/* private fields */}

impl ReturnFlags {
    fn new_with_reverted(has_reverted: bool) -> Self {
        unimplemented!()
    }
}

fn return_value<R>(return_flags: ReturnFlags, return_value: &R) -> ! {
    unimplemented!()
}

impl ConstructorsReturnValue {
    /// Infallible constructor
    pub fn new(init_value: bool) -> Self {
        Self { value: init_value }
    }

    /// Fallible constructor
    pub fn try_new(succeed: bool) -> Result<Self, ConstructorError> {
        if succeed {
            Ok(Self::new(true))
        } else {
            Err(ConstructorError)
        }
    }

    /// A constructor which reverts and fills the output buffer with an erroneously
    /// encoded return value.
    pub fn revert_new(_init_value: bool) -> Self {
        return_value::<ConstructorResult<AccountId>>(
            ReturnFlags::new_with_reverted(true),
            &Ok(AccountId::from([0u8; 32])),
        )
    }

    /// A constructor which reverts and fills the output buffer with an erroneously
    /// encoded return value.
    pub fn try_revert_new(init_value: bool) -> Result<Self, ConstructorError> {
        let value = if init_value {
            Ok(Ok(AccountId::from([0u8; 32])))
        } else {
            Err(LangError::CouldNotReadInput)
        };

        return_value::<ConstructorResult<Result<AccountId, ConstructorError>>>(
            ReturnFlags::new_with_reverted(true),
            &value,
        )
    }

    /// Returns the current value of the contract storage.
    pub fn get_value(&self) -> bool {
        self.value
    }
}
