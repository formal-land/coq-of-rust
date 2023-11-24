#[ink::contract]
pub mod flipper {
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

    mod tests {
        use super::*;

        fn default_works() {
            let flipper = Flipper::new_default();
            assert!(!flipper.get());
        }

        fn it_works() {
            let mut flipper = Flipper::new(false);
            assert!(!flipper.get());
            flipper.flip();
            assert!(flipper.get());
        }
    }
}
