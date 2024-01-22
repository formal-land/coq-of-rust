(* Generated by coq-of-rust *)
Require Import CoqOfRust.CoqOfRust.

(*
fn some_number() -> Option<u32> {
    Some(42)
}
*)
Parameter some_number : M (core.option.Option.t u32.t).

(*
fn main() {
    match some_number() {
        // Got `Some` variant, match if its value, bound to `n`,
        // is equal to 42.
        Some(n @ 42) => println!("The Answer: {}!", n),
        // Match any other number.
        Some(n) => println!("Not interesting... {}", n),
        // Match anything else (`None` variant).
        _ => (),
    }
}
*)
(* #[allow(dead_code)] - function was ignored by the compiler *)
Parameter main : M unit.