#![allow(unused)]
fn main() {
    use std::arch::asm;

    let cmd = 0xd1;
    unsafe {
        asm!("out 0x64, eax", in("eax") cmd);
    }
}
