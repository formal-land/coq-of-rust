#[derive(Default, Clone, Copy)]
struct AccountId(u128);

type Balance = u128;

struct Env {
    caller: AccountId,
}

impl Env {
    fn caller(&self) -> AccountId {
        self.caller
    }

    fn balance(&self) -> Balance {
        unimplemented!()
    }

    fn transfer(&mut self, _to: AccountId, _value: Balance) -> Result<(), ()> {
        unimplemented!()
    }

    fn transferred_value(&self) -> Balance {
        unimplemented!()
    }
}

/// No storage is needed for this simple contract.
pub struct GiveMe {}

impl GiveMe {
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

    /// Transfers `value` amount of tokens to the caller.
    ///
    /// # Errors
    ///
    /// - Panics in case the requested transfer exceeds the contract balance.
    /// - Panics in case the requested transfer would have brought this contract's
    ///   balance below the minimum balance (i.e. the chain's existential deposit).
    /// - Panics in case the transfer failed for another reason.
    pub fn give_me(&mut self, value: Balance) {
        println!("requested value: {}", value);
        println!("contract balance: {}", self.env().balance());

        assert!(value <= self.env().balance(), "insufficient funds!");

        if self.env().transfer(self.env().caller(), value).is_err() {
            panic!(
                "requested transfer failed. this can be the case if the contract does not\
                 have sufficient free funds or if the transfer would have brought the\
                 contract's balance below minimum balance."
            )
        }
    }

    /// Asserts that the token amount sent as payment with this call
    /// is exactly `10`. This method will fail otherwise, and the
    /// transaction would then be reverted.
    ///
    /// # Note
    ///
    /// The method needs to be annotated with `payable`; only then it is
    /// allowed to receive value as part of the call.
    pub fn was_it_ten(&self) {
        println!("received payment: {}", self.env().transferred_value());
        assert!(self.env().transferred_value() == 10, "payment was not ten");
    }
}
