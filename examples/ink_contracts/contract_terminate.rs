#[derive(Default, Clone, Copy)]
struct AccountId(u128);

struct Env {
    caller: AccountId,
}

impl Env {
    fn caller(&self) -> AccountId {
        self.caller
    }

    fn terminate_contract(&self, _account: AccountId) {
        unimplemented!()
    }
}

/// No storage is needed for this simple contract.
pub struct JustTerminate {}

impl JustTerminate {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    /// Creates a new instance of this contract.
    pub fn new() -> Self {
        Self {}
    }

    /// Terminates with the caller as beneficiary.
    pub fn terminate_me(&mut self) {
        self.env().terminate_contract(self.env().caller());
    }
}
