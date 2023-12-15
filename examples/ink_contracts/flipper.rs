pub struct Flipper {
    value: bool,
}

impl Flipper {
    /// Creates a new flipper smart contract initialized with the given value.
    pub fn new(init_value: bool) -> Self {
        Self { value: init_value }
    }

    /// Creates a new flipper smart contract initialized to `false`.
    pub fn new_default() -> Self {
        Self::new(Default::default())
    }

    /// Flips the current value of the Flipper's boolean.
    pub fn flip(&mut self) {
        self.value = !self.value;
    }

    /// Returns the current value of the Flipper's boolean.
    pub fn get(&self) -> bool {
        self.value
    }
}
