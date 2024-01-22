(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    use std::arch::asm;

    fn mul(a: u64, b: u64) -> u128 {
        let lo: u64;
        let hi: u64;

        unsafe {
            asm!(
                // The x86 mul instruction takes rax as an implicit input and writes
                // the 128-bit result of the multiplication to rax:rdx.
                "mul {}",
                in(reg) a,
                inlateout("rax") b => lo,
                lateout("rdx") hi
            );
        }

        ((hi as u128) << 64) + lo as u128
    }
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main : M unit := M.pure tt.

(*
    fn mul(a: u64, b: u64) -> u128 {
        let lo: u64;
        let hi: u64;

        unsafe {
            asm!(
                // The x86 mul instruction takes rax as an implicit input and writes
                // the 128-bit result of the multiplication to rax:rdx.
                "mul {}",
                in(reg) a,
                inlateout("rax") b => lo,
                lateout("rdx") hi
            );
        }

        ((hi as u128) << 64) + lo as u128
    }
*)
Definition mul (a : u64.t) (b : u64.t) : M u128.t :=
  let* a := M.alloc a in
  let* b := M.alloc b in
  let* lo := M.copy (DeclaredButUndefinedVariable (A := u64.t)) in
  let* hi := M.copy (DeclaredButUndefinedVariable (A := u64.t)) in
  let* _ : M.Val unit :=
    let _ : M.Val unit := InlineAssembly in
    M.alloc tt in
  let* α0 : u64.t := M.read hi in
  let* α1 : u128.t :=
    BinOp.Panic.shl (rust_cast α0) ((Integer.of_Z 64) : i32.t) in
  let* α2 : u64.t := M.read lo in
  let* α3 : u128.t := BinOp.Panic.add α1 (rust_cast α2) in
  let* α0 : M.Val u128.t := M.alloc α3 in
  M.read α0.