#[derive(Default, Clone, Copy)]
struct AccountId(u128);

type Balance = u128;

type Hash = [u8; 32];

pub enum LangError {
    CouldNotReadInput,
    AnotherError,
}

pub struct Selector {/* private fields */}

impl Selector {
    fn new(bytes: [u8; 4]) -> Self {
        unimplemented!()
    }
}

#[derive(Default)]
pub struct CallBuilderTest {}

impl CallBuilderTest {
    pub fn new() -> Self {
        Default::default()
    }

    /// Call a contract using the `CallBuilder`.
    ///
    /// Since we can't use the `CallBuilder` in a test environment directly we need
    /// this wrapper to test things like crafting calls with invalid
    /// selectors.
    ///
    /// We also wrap the output in an `Option` since we can't return a `Result`
    /// directly from a contract message without erroring out ourselves.
    #[allow(unreachable_code)]
    pub fn call(&mut self, address: AccountId, selector: [u8; 4]) -> Option<LangError> {
        // let result = build_call::<DefaultEnvironment>()
        //     .call(address)
        //     .exec_input(ExecutionInput::new(Selector::new(selector)))
        //     .returns::<()>()
        //     .try_invoke()
        //     .expect("Error from the Contracts pallet.");
        let result: Result<(), LangError> = todo!();

        match result {
            Ok(_) => None,
            Err(e @ LangError::CouldNotReadInput) => Some(e),
            Err(_) => {
                unimplemented!("No other `LangError` variants exist at the moment.")
            }
        }
    }

    /// Call a contract using the `CallBuilder`.
    ///
    /// Since we can't use the `CallBuilder` in a test environment directly we need
    /// this wrapper to test things like crafting calls with invalid
    /// selectors.
    ///
    /// This message does not allow the caller to handle any `LangErrors`, for that
    /// use the `call` message instead.
    pub fn invoke(&mut self, address: AccountId, selector: [u8; 4]) {
        // use ink::env::call::build_call;

        // build_call::<DefaultEnvironment>()
        //     .call(address)
        //     .exec_input(ExecutionInput::new(Selector::new(selector)))
        //     .returns::<()>()
        //     .invoke()
    }

    /// Instantiate a contract using the `CreateBuilder`.
    ///
    /// Since we can't use the `CreateBuilder` in a test environment directly we need
    /// this wrapper to test things like crafting calls with invalid
    /// selectors.
    ///
    /// We also wrap the output in an `Option` since we can't return a `Result`
    /// directly from a contract message without erroring out ourselves.
    pub fn call_instantiate(
        &mut self,
        code_hash: Hash,
        selector: [u8; 4],
        init_value: bool,
    ) -> Option<LangError> {
        // let mut params = ConstructorsReturnValueRef::new(init_value)
        //     .code_hash(code_hash)
        //     .gas_limit(0)
        //     .endowment(0)
        //     .salt_bytes(&[0xDE, 0xAD, 0xBE, 0xEF])
        //     .params();

        // params.update_selector(Selector::new(selector));

        // let result = params
        //     .try_instantiate()
        //     .expect("Error from the Contracts pallet.");

        // match result {
        //     Ok(_) => None,
        //     Err(e @ LangError::CouldNotReadInput) => Some(e),
        //     Err(_) => {
        //         unimplemented!("No other `LangError` variants exist at the moment.")
        //     }
        // }
        None
    }

    /// Attempt to instantiate a contract using the `CreateBuilder`.
    ///
    /// Since we can't use the `CreateBuilder` in a test environment directly we need
    /// this wrapper to test things like crafting calls with invalid
    /// selectors.
    ///
    /// We also wrap the output in an `Option` since we can't return a `Result`
    /// directly from a contract message without erroring out ourselves.
    pub fn call_instantiate_fallible(
        &mut self,
        code_hash: Hash,
        selector: [u8; 4],
        init_value: bool,
        // ) -> Option<Result<Result<AccountId, constructors_return_value::ConstructorError>, LangError>>
    ) -> Option<()> {
        // let mut params = ConstructorsReturnValueRef::try_new(init_value)
        //     .code_hash(code_hash)
        //     .gas_limit(0)
        //     .endowment(0)
        //     .salt_bytes(&[0xDE, 0xAD, 0xBE, 0xEF])
        //     .params();

        // params.update_selector(Selector::new(selector));

        // let lang_result = params
        //     .try_instantiate()
        //     .expect("Error from the Contracts pallet.");

        // Some(lang_result.map(|contract_result| {
        //     contract_result.map(|inner| ink::ToAccountId::to_account_id(&inner))
        // }))
        None
    }
}
