pub struct Incrementer {
    value: i32,
}

impl Incrementer {
    pub fn new(init_value: i32) -> Self {
        Self { value: init_value }
    }

    pub fn new_default() -> Self {
        Self::new(Default::default())
    }

    pub fn inc(&mut self, by: i32) {
        self.value += by;
    }

    pub fn get(&self) -> i32 {
        self.value
    }
}
