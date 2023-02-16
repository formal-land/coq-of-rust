#![allow(unused)]
fn main() {
    use std::arch::asm;

    let mut a: u64 = 4;
    let b: u64 = 4;
    let c: u64 = 4;
    unsafe {
        asm!(
            "add {0}, {1}",
            "add {0}, {2}",
            inout(reg) a,
            in(reg) b,
            in(reg) c,
        );
    }
    assert_eq!(a, 12);
}
