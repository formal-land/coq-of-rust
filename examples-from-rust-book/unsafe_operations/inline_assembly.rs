#![allow(unused)]
fn main() {
    use std::arch::asm;

    unsafe {
        asm!("nop");
    }
}
