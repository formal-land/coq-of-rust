Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.fmt.links.mod.
Require Import core.panicking.

(* pub const fn panic_fmt(fmt: fmt::Arguments<'_>) -> ! *)
Instance run_panic_fmt (fmt : Arguments.t) :
  Run.Trait panicking.panic_fmt [] [] [φ fmt] Empty_set.
Proof.
  constructor.
  run_symbolic.
Admitted.

(* pub const fn panic(expr: &'static str) -> ! *)
Instance run_panic (expr : Ref.t Pointer.Kind.Ref string) :
  Run.Trait panicking.panic [] [] [φ expr] Empty_set.
Proof.
  constructor.
  run_symbolic.
Admitted.
