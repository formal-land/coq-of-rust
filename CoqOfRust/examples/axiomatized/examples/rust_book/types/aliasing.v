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
Parameter main : M unit.