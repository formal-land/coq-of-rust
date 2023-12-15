pub struct Flipper {
    value: bool,
}

#[derive(Debug)]
pub struct FlipperError;

impl Flipper {
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

    /// Flips the current value of the Flipper's boolean.
    pub fn flip(&mut self) {
        self.value = !self.value;
    }

    /// Returns the current value of the Flipper's boolean.
    pub fn get(&self) -> bool {
        self.value
    }

    /// Flips the current value of the Flipper's boolean.
    ///
    /// We should see the state being reverted here, no write should occur.
    #[allow(clippy::result_unit_err)]
    pub fn err_flip(&mut self) -> Result<(), ()> {
        self.flip();
        Err(())
    }
}
