#![allow(unused)]
fn main() {
    use std::arch::asm;

    let x: u64 = 3;
    let y: u64;
    unsafe {
        asm!("add {0}, 5", inout(reg) x => y);
    }
    assert_eq!(y, 8);
}
