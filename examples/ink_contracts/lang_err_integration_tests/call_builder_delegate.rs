type Hash = [u8; 32];

pub enum LangError {
    CouldNotReadInput,
}

#[derive(Default)]
pub struct CallBuilderDelegateTest {
    /// Since we're going to `DelegateCall` into the `incrementer` contract, we need
    /// to make sure our storage layout matches.
    value: i32,
}

impl CallBuilderDelegateTest {
    pub fn new(value: i32) -> Self {
        Self { value }
    }

    /// Call a contract using the `CallBuilder`.
    ///
    /// Since we can't use the `CallBuilder` in a test environment directly we need
    /// this wrapper to test things like crafting calls with invalid
    /// selectors.
    ///
    /// We also wrap the output in an `Option` since we can't return a `Result`
    /// directly from a contract message without erroring out ourselves.
    pub fn delegate(&mut self, code_hash: Hash, selector: [u8; 4]) -> Option<LangError> {
        // let result = build_call::<DefaultEnvironment>()
        //     .delegate(code_hash)
        //     .exec_input(ExecutionInput::new(Selector::new(selector)))
        //     .returns::<bool>()
        //     .try_invoke()
        //     .expect("Error from the Contracts pallet.");

        // match result {
        //     Ok(_) => None,
        //     Err(e @ ink::LangError::CouldNotReadInput) => Some(e),
        //     Err(_) => {
        //         unimplemented!("No other `LangError` variants exist at the moment.")
        //     }
        // }
        None
    }

    /// Call a contract using the `CallBuilder`.
    ///
    /// Since we can't use the `CallBuilder` in a test environment directly we need
    /// this wrapper to test things like crafting calls with invalid
    /// selectors.
    ///
    /// This message does not allow the caller to handle any `LangErrors`, for that
    /// use the `call` message instead.
    pub fn invoke(&mut self, code_hash: Hash, selector: [u8; 4]) -> i32 {
        // use ink::env::call::build_call;

        // build_call::<DefaultEnvironment>()
        //     .delegate(code_hash)
        //     .exec_input(ExecutionInput::new(Selector::new(selector)))
        //     .returns::<i32>()
        //     .invoke()
        0
    }
}
