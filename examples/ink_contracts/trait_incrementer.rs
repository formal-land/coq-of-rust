pub trait Increment {
    /// Increments the current value of the implementer by one (1).
    fn inc(&mut self);

    /// Returns the current value of the implementer.
    fn get(&self) -> u64;
}

/// Allows to reset the current value.
pub trait Reset {
    /// Resets the current value to zero.
    fn reset(&mut self);
}

/// A concrete incrementer smart contract.
pub struct Incrementer {
    value: u64,
}

impl Incrementer {
    /// Creates a new incrementer smart contract initialized with zero.
    pub fn new(init_value: u64) -> Self {
        Self { value: init_value }
    }

    /// Increases the value of the incrementer by an amount.
    pub fn inc_by(&mut self, delta: u64) {
        self.value += delta;
    }
}

impl Increment for Incrementer {
    fn inc(&mut self) {
        self.inc_by(1)
    }

    fn get(&self) -> u64 {
        self.value
    }
}

impl Reset for Incrementer {
    fn reset(&mut self) {
        self.value = 0;
    }
}
