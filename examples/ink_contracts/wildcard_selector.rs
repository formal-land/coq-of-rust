fn decode_input<T>() -> Result<T, ()> {
    unimplemented!()
}

pub struct WildcardSelector {}

impl WildcardSelector {
    /// Creates a new wildcard selector smart contract.
    #[allow(clippy::new_without_default)]
    pub fn new() -> Self {
        Self {}
    }

    /// Wildcard selector handles messages with any selector.
    pub fn wildcard(&mut self) {
        let (_selector, _message) = decode_input::<([u8; 4], String)>().unwrap();
        println!("Wildcard selector: {:?}, message: {}", _selector, _message);
    }

    /// Wildcard complement handles messages with a well-known reserved selector.
    pub fn wildcard_complement(&mut self, _message: String) {
        println!("Wildcard complement message: {}", _message);
    }
}
