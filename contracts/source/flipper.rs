#[ink::contract]
pub mod flipper {
    // #[ink(storage)]
    pub struct Flipper {
        value: bool,
    }

    impl Flipper {
        pub fn new(init_value: bool) -> Self {
            Self { value: init_value }
        }

        pub fn new_default() -> Self {
            Self::new(Default::default())
        }

        pub fn flip(&mut self) {
            self.value = !self.value;
        }

        pub fn get(&self) -> bool {
            self.value
        }
    }
}
