#[derive(Default, Clone, Copy)]
struct AccountId(u128);

type Balance = u128;

struct Env {
    caller: AccountId,
}

enum MultiAddress<AccountId, AccountIndex> {}

impl std::convert::From<AccountId> for MultiAddress<AccountId, ()> {
    fn from(_value: AccountId) -> Self {
        unimplemented!()
    }
}

enum BalancesCall {
    /// This index can be found by investigating the pallet dispatchable API. In your
    /// pallet code, look for `#[pallet::call]` section and check
    /// `#[pallet::call_index(x)]` attribute of the call. If these attributes are
    /// missing, use source-code order (0-based).
    Transfer {
        dest: MultiAddress<AccountId, ()>,
        value: u128,
    },
}

/// A part of the runtime dispatchable API.
///
/// For now, `ink!` doesn't provide any support for exposing the real `RuntimeCall` enum,
/// which fully describes the composed API of all the pallets present in runtime. Hence,
/// in order to use `call-runtime` functionality, we have to provide at least a partial
/// object, which correctly encodes the target extrinsic.
///
/// You can investigate the full `RuntimeCall` definition by either expanding
/// `construct_runtime!` macro application or by using secondary tools for reading chain
/// metadata, like `subxt`.
enum RuntimeCall {
    /// This index can be found by investigating runtime configuration. You can check the
    /// pallet order inside `construct_runtime!` block and read the position of your
    /// pallet (0-based).
    ///
    ///
    /// [See here for more.](https://substrate.stackexchange.com/questions/778/how-to-get-pallet-index-u8-of-a-pallet-in-runtime)
    Balances(BalancesCall),
}

/// A trivial contract with a single message, that uses `call-runtime` API for
/// performing native token transfer.
#[derive(Default)]
pub struct RuntimeCaller;

#[derive(Debug, PartialEq, Eq)]
pub enum RuntimeError {
    CallRuntimeFailed,
}

enum EnvError {
    CallRuntimeFailed,
    AnotherKindOfError,
}

impl From<EnvError> for RuntimeError {
    fn from(e: EnvError) -> Self {
        match e {
            EnvError::CallRuntimeFailed => RuntimeError::CallRuntimeFailed,
            _ => panic!("Unexpected error from `pallet-contracts`."),
        }
    }
}

impl Env {
    fn call_runtime<Call>(&self, _call: &Call) -> Result<(), EnvError> {
        unimplemented!()
    }
}

impl RuntimeCaller {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    /// The constructor is `payable`, so that during instantiation it can be given
    /// some tokens that will be further transferred with
    /// `transfer_through_runtime` message.
    pub fn new() -> Self {
        Default::default()
    }

    /// Tries to transfer `value` from the contract's balance to `receiver`.
    ///
    /// Fails if:
    ///  - called in the off-chain environment
    ///  - the chain forbids contracts to call `Balances::transfer` (`CallFilter` is
    ///    too restrictive)
    ///  - after the transfer, `receiver` doesn't have at least existential deposit
    ///  - the contract doesn't have enough balance
    pub fn transfer_through_runtime(
        &mut self,
        receiver: AccountId,
        value: Balance,
    ) -> Result<(), RuntimeError> {
        self.env()
            .call_runtime(&RuntimeCall::Balances(BalancesCall::Transfer {
                dest: receiver.into(),
                value,
            }))
            .map_err(Into::into)
    }

    /// Tries to trigger `call_runtime` API with rubbish data.
    ///
    /// # Note
    ///
    /// This message is for testing purposes only.
    pub fn call_nonexistent_extrinsic(&mut self) -> Result<(), RuntimeError> {
        self.env().call_runtime(&()).map_err(Into::into)
    }
}
