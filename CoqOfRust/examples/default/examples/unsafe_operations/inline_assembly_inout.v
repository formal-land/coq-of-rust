(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn main() {
    use std::arch::asm;

    let x: u64 = 3;
    let y: u64;
    unsafe {
        asm!("add {0}, 5", inout(reg) x => y);
    }
    assert_eq!(y, 8);
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main : M unit :=
  let* x : M.Val u64.t := M.alloc (Integer.of_Z 3) in
  let* y : M.Val unit := M.alloc tt in
  let* _ : M.Val unit :=
    let _ : M.Val unit := InlineAssembly in
    M.alloc tt in
  let* _ : M.Val unit :=
    let* α0 : M.Val u64.t := M.alloc (Integer.of_Z 8) in
    match (borrow y, borrow α0) with
    | (left_val, right_val) =>
      let* right_val := M.alloc right_val in
      let* left_val := M.alloc left_val in
      let* α0 : ref u64.t := M.read left_val in
      let* α1 : u64.t := M.read (deref α0) in
      let* α2 : ref u64.t := M.read right_val in
      let* α3 : u64.t := M.read (deref α2) in
      if (use (UnOp.not (BinOp.Pure.eq α1 α3)) : bool) then
        let* kind : M.Val core.panicking.AssertKind.t :=
          M.alloc core.panicking.AssertKind.Eq in
        let* _ : M.Val never.t :=
          let* α0 : core.panicking.AssertKind.t := M.read kind in
          let* α1 : ref u64.t := M.read left_val in
          let* α2 : ref u64.t := M.read right_val in
          let* α3 : never.t :=
            core.panicking.assert_failed α0 α1 α2 core.option.Option.None in
          M.alloc α3 in
        let* α0 : M.Val unit := M.alloc tt in
        let* α1 := M.read α0 in
        let* α2 : unit := never_to_any α1 in
        M.alloc α2
      else
        M.alloc tt
    end in
  let* α0 : M.Val unit := M.alloc tt in
  M.read α0.