#[derive(Default, Clone, Copy)]
struct AccountId(u128);

type Hash = [u8; 32];

enum Error {}

pub struct OtherContract {
    value: bool,
}

impl OtherContract {
    pub fn new(init_value: bool) -> Self {
        Self { value: init_value }
    }

    pub fn flip(&mut self) {
        self.value = !self.value;
    }

    pub fn get(&self) -> bool {
        self.value
    }
}

pub struct BasicContractCaller {
    /// We specify that our contract will store a reference to the `OtherContract`.
    other_contract: OtherContract,
}

impl BasicContractCaller {
    /// In order to use the `OtherContract` we first need to **instantiate** it.
    ///
    /// To do this we will use the uploaded `code_hash` of `OtherContract`.
    #[allow(unreachable_code)]
    pub fn new(other_contract_code_hash: Hash) -> Self {
        // let other_contract = OtherContract::new(true)
        //     .code_hash(other_contract_code_hash)
        //     .endowment(0)
        //     .salt_bytes([0xDE, 0xAD, 0xBE, 0xEF])
        //     .instantiate();
        let other_contract = todo!();

        Self { other_contract }
    }

    /// Using the `ContractRef` we can call all the messages of the `OtherContract` as
    /// if they were normal Rust methods (because at the end of the day, they
    /// are!).
    pub fn flip_and_get(&mut self) -> bool {
        self.other_contract.flip();
        self.other_contract.get()
    }
}
