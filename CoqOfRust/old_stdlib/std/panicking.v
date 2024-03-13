Require Import CoqOfRust.lib.lib.

(* pub const fn begin_panic<M: Any + Send>(msg: M) -> ! *)
Parameter begin_panic : forall {M' : Set}, M' -> M never.t.
