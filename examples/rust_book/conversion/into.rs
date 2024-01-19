use std::convert::From;

struct Number {
    value: i32,
}

impl From<i32> for Number {
    fn from(item: i32) -> Self {
        Number { value: item }
    }
}

fn main() {
    <i32 as std::convert::Into<Number>>::into(5);
}
