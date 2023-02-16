#![allow(unused)]
fn main() {
    use std::arch::asm;

    extern "C" fn foo(arg: i32) -> i32 {
        println!("arg = {}", arg);
        arg * 2
    }

    fn call_foo(arg: i32) -> i32 {
        unsafe {
            let result;
            asm!(
                "call {}",
                // Function pointer to call
                in(reg) foo,
                // 1st argument in rdi
                in("rdi") arg,
                // Return value in rax
                out("rax") result,
                // Mark all registers which are not preserved by the "C" calling
                // convention as clobbered.
                clobber_abi("C"),
            );
            result
        }
    }
}
