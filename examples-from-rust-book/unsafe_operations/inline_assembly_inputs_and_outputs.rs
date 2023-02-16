#![allow(unused)]
fn main() {
    use std::arch::asm;

    let x: u64;
    unsafe {
        asm!("mov {}, 5", out(reg) x);
    }
    assert_eq!(x, 5);
}
