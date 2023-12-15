#[derive(Default, Clone, Copy)]
struct AccountId(u128);

type Balance = u128;

type Hash = [u8; 32];

struct Env {
    caller: AccountId,
}

pub struct FlipperRef {
    value: bool,
}

#[derive(Debug)]
pub struct FlipperError;

impl FlipperRef {
    fn init_env() -> Env {
        unimplemented!()
    }

    fn env(&self) -> Env {
        Self::init_env()
    }

    /// Creates a new integration_flipper smart contract initialized with the given
    /// value.
    pub fn new(init_value: bool) -> Self {
        Self { value: init_value }
    }

    /// Creates a new integration_flipper smart contract initialized to `false`.
    pub fn new_default() -> Self {
        Self::new(Default::default())
    }

    /// Attemps to create a new integration_flipper smart contract initialized with
    /// the given value.
    pub fn try_new(succeed: bool) -> Result<Self, FlipperError> {
        if succeed {
            Ok(Self::new(true))
        } else {
            Err(FlipperError)
        }
    }

    pub fn flip(&mut self) {
        self.value = !self.value;
    }

    pub fn get(&self) -> bool {
        self.value
    }
}

pub struct ContractRef {
    flipper: FlipperRef,
}

impl ContractRef {
    pub fn new(version: u32, flipper_code_hash: Hash) -> Self {
        let salt = version.to_le_bytes();
        let flipper = FlipperRef::new_default();
        // .endowment(0)
        // .code_hash(flipper_code_hash)
        // .salt_bytes(salt)
        // .instantiate();

        Self { flipper }
    }

    pub fn try_new(version: u32, flipper_code_hash: Hash, succeed: bool) -> Self {
        let salt = version.to_le_bytes();
        let flipper = FlipperRef::try_new(succeed).unwrap();
        // .endowment(0)
        // .code_hash(flipper_code_hash)
        // .salt_bytes(salt)
        // .instantiate()
        // .unwrap_or_else(|error| {
        //     panic!(
        //         "Received an error from the Flipper constructor while instantiating \
        //              Flipper {error:?}"
        //     )
        // });

        Self { flipper }
    }

    pub fn flip(&mut self) {
        self.flipper.flip();
    }

    // pub fn flip_check(&mut self) {
    //     self.flipper
    //         .try_flip()
    //         .expect("The ink! codegen should've produced a valid call.");
    // }

    pub fn get(&mut self) -> bool {
        self.flipper.get()
    }

    // pub fn get_check(&mut self) -> bool {
    //     self.flipper
    //         .try_get()
    //         .expect("The ink! codegen should've produced a valid call.")
    // }
}
