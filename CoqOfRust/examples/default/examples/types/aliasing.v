(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

Ltac NanoSecond := exact u64.t.

Ltac Inch := exact u64.t.

Ltac U64 := exact u64.t.

(*
fn main() {
    // `NanoSecond` = `Inch` = `U64` = `u64`.
    let nanoseconds: NanoSecond = 5 as U64;
    let inches: Inch = 2 as U64;

    // Note that type aliases *don't* provide any extra type safety, because
    // aliases are *not* new types
    println!(
        "{} nanoseconds + {} inches = {} unit?",
        nanoseconds,
        inches,
        nanoseconds + inches
    );
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Definition main : M unit :=
  let* nanoseconds : M.Val u64.t := M.alloc (use (Integer.of_Z 5)) in
  let* inches : M.Val u64.t := M.alloc (use (Integer.of_Z 2)) in
  let* _ : M.Val unit :=
    let* _ : M.Val unit :=
      let* α0 : M.Val (array (ref str.t)) :=
        M.alloc
          [
            mk_str "";
            mk_str " nanoseconds + ";
            mk_str " inches = ";
            mk_str " unit?
"
          ] in
      let* α1 : M.Val (ref (array (ref str.t))) := M.alloc (borrow α0) in
      let* α2 : ref (slice (ref str.t)) :=
        M.read (pointer_coercion "Unsize" α1) in
      let* α3 : core.fmt.rt.Argument.t :=
        core.fmt.rt.Argument.t::["new_display"] (borrow nanoseconds) in
      let* α4 : M.Val core.fmt.rt.Argument.t := M.alloc α3 in
      let* α5 : core.fmt.rt.Argument.t :=
        core.fmt.rt.Argument.t::["new_display"] (borrow inches) in
      let* α6 : M.Val core.fmt.rt.Argument.t := M.alloc α5 in
      let* α7 : u64.t := M.read nanoseconds in
      let* α8 : u64.t := M.read inches in
      let* α9 : u64.t := BinOp.Panic.add α7 α8 in
      let* α10 : M.Val u64.t := M.alloc α9 in
      let* α11 : core.fmt.rt.Argument.t :=
        core.fmt.rt.Argument.t::["new_display"] (borrow α10) in
      let* α12 : M.Val core.fmt.rt.Argument.t := M.alloc α11 in
      let* α13 : M.Val (array core.fmt.rt.Argument.t) :=
        M.alloc [ α4; α6; α12 ] in
      let* α14 : M.Val (ref (array core.fmt.rt.Argument.t)) :=
        M.alloc (borrow α13) in
      let* α15 : ref (slice core.fmt.rt.Argument.t) :=
        M.read (pointer_coercion "Unsize" α14) in
      let* α16 : core.fmt.Arguments.t :=
        core.fmt.Arguments.t::["new_v1"] α2 α15 in
      let* α17 : unit := std.io.stdio._print α16 in
      M.alloc α17 in
    M.alloc tt in
  let* α0 : M.Val unit := M.alloc tt in
  M.read α0.