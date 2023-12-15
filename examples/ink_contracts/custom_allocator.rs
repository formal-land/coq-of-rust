pub struct CustomAllocator {
    /// Stores a single `bool` value on the storage.
    ///
    /// # Note
    ///
    /// We're using a `Vec` here as it allocates its elements onto the heap, as
    /// opposed to the stack. This allows us to demonstrate that our new
    /// allocator actually works.
    value: Vec<bool>,
}

impl CustomAllocator {
    /// Constructor that initializes the `bool` value to the given `init_value`.
    pub fn new(init_value: bool) -> Self {
        Self {
            value: vec![init_value],
        }
    }

    /// Creates a new flipper smart contract initialized to `false`.
    pub fn default() -> Self {
        Self::new(Default::default())
    }

    /// A message that can be called on instantiated contracts.
    /// This one flips the value of the stored `bool` from `true`
    /// to `false` and vice versa.
    pub fn flip(&mut self) {
        self.value[0] = !self.value[0];
    }

    /// Simply returns the current value of our `bool`.
    pub fn get(&self) -> bool {
        self.value[0]
    }
}
