#![allow(unused)]
fn main() {
    use std::arch::asm;

    let mut x: u64 = 3;
    unsafe {
        asm!("add {0}, 5", inout(reg) x);
    }
    assert_eq!(x, 8);
}
