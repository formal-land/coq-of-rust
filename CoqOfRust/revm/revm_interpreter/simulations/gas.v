Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import simulations.M.
Require Import revm_interpreter.links.gas.

Import Run.

(* Module Impl_Default_for_MemoryGas.
  Definition default : MemoryGas.t := {|
    MemoryGas.words_num := {| Integer.value := 0 |};
    MemoryGas.expansion_cost := {| Integer.value := 0 |};
  |}.
End Impl_Default_for_MemoryGas. *)

Module Impl_MemoryGas.
  (* Definition Self : Set := MemoryGas.t. *)

  (* Definition new : Self := Impl_Default_for_MemoryGas.default. *)

  Compute links.M.evaluate Impl_MemoryGas.run_new.(Run.run_f).

  Definition run_new :
    {{ [] 🌲 links.M.evaluate Impl_MemoryGas.run_new.(Run.run_f) }}.
  Proof.
    constructor.
  Defined.

  Compute M.evaluate run_new tt.
End Impl_MemoryGas.

Module Impl_Gas.
  (* Definition Self : Set := Gas.t. *)

  (*
      pub const fn new(limit: u64) -> Self {
          Self {
              limit,
              remaining: limit,
              refunded: 0,
              memory: MemoryGas::new(),
          }
      }
  *)
  (* Definition new (limit : U64.t) : Self := {|
    Gas.limit := limit;
    Gas.remaining := limit;
    Gas.refunded := {| Integer.value := 0 |};
    Gas.memory := Impl_MemoryGas.new;
  |}. *)

  Compute links.M.evaluate ((Impl_Gas.run_new {| Integer.value := 12 |}).(Run.run_f)).

  Definition run_new (limit : U64.t) :
    {{ [] 🌲 links.M.evaluate (Impl_Gas.run_new limit).(Run.run_f) }}.
  Proof.
    cbn.
    apply Run.Call. {
      apply Impl_MemoryGas.run_new.
    }
    intros []; cbn; [|apply Run.Pure].
    apply Run.Pure.
  Defined.

  Compute M.evaluate (run_new {| Integer.value := 12 |}) tt.

  (*
      pub const fn new_spent(limit: u64) -> Self {
          Self {
              limit,
              remaining: 0,
              refunded: 0,
              memory: MemoryGas::new(),
          }
      }
  *)
  Definition run_new_spent (limit : U64.t) :
    {{ [] 🌲 links.M.evaluate (Impl_Gas.run_new_spent limit).(Run.run_f) }}.
  Proof.
    cbn.
    apply Run.Call. {
      apply Impl_MemoryGas.run_new.
    }
    intros []; cbn; [|apply Run.Pure].
    apply Run.Pure.
  Defined.

  (*
      pub const fn limit(&self) -> u64 {
          self.limit
      }
  *)
  (* Definition limit (self : Self) : U64.t :=
    self.(Gas.limit). *)

  (* Lemma run_limit (self : Self) :
    {{
      M.evaluate (Impl_Gas.run_limit self) 🌲
      Output.Success (limit self)
    }}. *)
End Impl_Gas.
