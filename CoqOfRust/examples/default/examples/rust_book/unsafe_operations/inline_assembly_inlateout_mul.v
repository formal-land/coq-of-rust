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
Definition main (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
  match ε, τ, α with
  | [], [], [] => ltac:(M.monadic (Value.Tuple []))
  | _, _, _ => M.impossible "wrong number of arguments"
  end.

Global Instance Instance_IsFunction_main :
  M.IsFunction.C "inline_assembly_inlateout_mul::main" main.
Admitted.
Global Typeclasses Opaque main.

Module main.
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
  Definition mul (ε : list Value.t) (τ : list Ty.t) (α : list Value.t) : M :=
    match ε, τ, α with
    | [], [], [ a; b ] =>
      ltac:(M.monadic
        (let a := M.alloc (| Ty.path "u64", a |) in
        let b := M.alloc (| Ty.path "u64", b |) in
        M.read (|
          let lo := M.read (| Value.DeclaredButUndefined |) in
          let hi := M.read (| Value.DeclaredButUndefined |) in
          let~ _ : Ty.tuple [] :=
            M.read (|
              let~ _ : Ty.tuple [] := M.read (| InlineAssembly |) in
              M.alloc (| Ty.tuple [], Value.Tuple [] |)
            |) in
          M.alloc (|
            Ty.path "u128",
            M.call_closure (|
              Ty.path "u128",
              BinOp.Wrap.add,
              [
                M.call_closure (|
                  Ty.path "u128",
                  BinOp.Wrap.shl,
                  [ M.cast (Ty.path "u128") (M.read (| hi |)); Value.Integer IntegerKind.I32 64 ]
                |);
                M.cast (Ty.path "u128") (M.read (| lo |))
              ]
            |)
          |)
        |)))
    | _, _, _ => M.impossible "wrong number of arguments"
    end.
  
  Global Instance Instance_IsFunction_mul :
    M.IsFunction.C "inline_assembly_inlateout_mul::main::mul" mul.
  Admitted.
  Global Typeclasses Opaque mul.
End main.
