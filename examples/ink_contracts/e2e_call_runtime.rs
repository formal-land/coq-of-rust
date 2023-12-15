#[derive(Default, Clone, Copy)]
struct AccountId(u128);

type Balance = u128;

struct Env {
    caller: AccountId,
}

impl Env {
    fn balance(&self) -> Balance {
        unimplemented!()
    }
}

#[derive(Default)]
pub struct Contract {}

impl Contract {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    pub fn new() -> Self {
        Self {}
    }

    pub fn get_contract_balance(&self) -> Balance {
        self.env().balance()
    }
}
