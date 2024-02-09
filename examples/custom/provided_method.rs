trait ProvidedAndRequired {
    fn required(&self) -> i32;
    fn provided(&self) -> i32 {
        42 + self.required()
    }
}

impl ProvidedAndRequired for i32 {
    fn required(&self) -> i32 {
        *self
    }
}

impl ProvidedAndRequired for u32 {
    fn required(&self) -> i32 {
        *self as i32
    }

    fn provided(&self) -> i32 {
        0
    }
}

fn main() {
    let x = 5;
    assert_eq!(x.provided(), 47);
    let y = 5u32;
    assert_eq!(y.provided(), 0);
}
