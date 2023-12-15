pub trait Flip {
    /// Flips the current value of the Flipper's boolean.
    fn flip(&mut self);

    /// Returns the current value of the Flipper's boolean.
    fn get(&self) -> bool;
}

pub struct Flipper {
    value: bool,
}

impl Flipper {
    /// Creates a new flipper smart contract initialized to `false`.
    pub fn new() -> Self {
        Self {
            value: Default::default(),
        }
    }
}

impl Flip for Flipper {
    fn flip(&mut self) {
        self.value = !self.value;
    }

    fn get(&self) -> bool {
        self.value
    }
}
