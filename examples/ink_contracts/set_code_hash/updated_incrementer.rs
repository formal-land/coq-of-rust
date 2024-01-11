#[derive(Default, Clone, Copy)]
struct AccountId(u128);

type Hash = [u8; 32];

enum Error {}

struct Env {
    caller: AccountId,
}

impl Env {
    fn set_code_hash<E>(&self, code_hash: &E) -> Result<(), Error> {
        unimplemented!()
    }
}

/// Track a counter in storage.
///
/// # Note
///
/// We have kept the same storage layout as in our original `incrementer` contract.
///
/// Had we changed `count` to, for example, an `AccountId` we would end up with
/// undefined behaviour in our contract.
pub struct Incrementer {
    count: u32,
}

impl Incrementer {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    /// Creates a new counter smart contract initialized with the given base value.
    ///
    /// # Note
    ///
    /// When upgrading using the `set_code_hash` workflow we only need to point to a
    /// contract's uploaded code hash, **not** an instantiated contract's
    /// `AccountId`.
    ///
    /// Because of this we will never actually call the constructor of this contract.
    pub fn new() -> Self {
        unreachable!("Constructors are not called when upgrading using `set_code_hash`.")
    }

    /// Increments the counter value which is stored in the contract's storage.
    ///
    /// # Note
    ///
    /// We use a different step size (4) here than in the original `incrementer`.
    pub fn inc(&mut self) {
        self.count += 4;
        println!(
            "The new count is {}, it was modified using the updated `new_incrementer` code.",
            self.count
        );
    }

    /// Returns the counter value which is stored in this contract's storage.
    pub fn get(&self) -> u32 {
        self.count
    }

    /// Modifies the code which is used to execute calls to this contract address
    /// (`AccountId`).
    ///
    /// We use this to upgrade the contract logic. We don't do any authorization here,
    /// any caller can execute this method.
    ///
    /// In a production contract you would do some authorization here!
    pub fn set_code(&mut self, code_hash: Hash) {
        self.env().set_code_hash(&code_hash).unwrap_or_else(|err| {
            panic!("Failed to `set_code_hash` to {code_hash:?} due to {err:?}")
        });
        println!("Switched code hash to {:?}.", code_hash);
    }
}
