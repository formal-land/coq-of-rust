trait Scale {
    fn scale(self, value: u32) -> u32;
}

struct Double;

struct Triple;

struct Offset;

trait Convert<T> {
    fn convert(self, value: T) -> u32;
}

impl Scale for Double {
    fn scale(self, value: u32) -> u32 {
        value * 2
    }
}

impl Scale for Triple {
    fn scale(self, value: u32) -> u32 {
        value * 3
    }
}

impl Convert<u32> for Offset {
    fn convert(self, value: u32) -> u32 {
        value + 1
    }
}

impl Convert<bool> for Offset {
    fn convert(self, value: bool) -> u32 {
        if value {
            10
        } else {
            0
        }
    }
}

fn choose<T>(condition: bool, left: T, right: T) -> T {
    if condition {
        left
    } else {
        right
    }
}

fn apply_scale<S: Scale>(strategy: S, value: u32) -> u32 {
    strategy.scale(value)
}

fn combine<A: Scale, B: Scale>(first: A, second: B, value: u32) -> u32 {
    apply_scale(first, value) + apply_scale(second, value)
}

fn apply_convert<T, C: Convert<T>>(converter: C, value: T) -> u32 {
    converter.convert(value)
}

pub fn compute() -> u32 {
    let value = choose(true, 5, 9);
    let scaled = combine(Double, Triple, value);
    let converted_number = apply_convert(Offset, value);
    let converted_flag = apply_convert(Offset, true);
    scaled + converted_number + converted_flag
}

fn main() {
    let _result = compute();
}
