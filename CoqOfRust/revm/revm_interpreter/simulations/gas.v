Require Import CoqOfRust.CoqOfRust.
Require Import links.M.
Require Import simulations.M.
Require Import revm_interpreter.links.gas.

Import Run.

Module Impl_Default_for_MemoryGas.
  Definition default : MemoryGas.t := {|
    MemoryGas.words_num := {| Integer.value := 0 |};
    MemoryGas.expansion_cost := {| Integer.value := 0 |};
  |}.
End Impl_Default_for_MemoryGas.

Module Impl_MemoryGas.
  Definition Self : Set := MemoryGas.t.

  Definition new : Self := Impl_Default_for_MemoryGas.default.

  Lemma run_new :
    {{
      M.evaluate Impl_MemoryGas.run_new 🌲
      SuccessOrPanic.to_output (SuccessOrPanic.Success new)
    }}.
  Proof.
    constructor.
  Qed.

  (* Lemma run_record_new_len *)
End Impl_MemoryGas.

Module Impl_Gas.
  Definition Self : Set := Gas.t.

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
  Definition new (limit : U64.t) : Self := {|
    Gas.limit := limit;
    Gas.remaining := limit;
    Gas.refunded := {| Integer.value := 0 |};
    Gas.memory := Impl_MemoryGas.new;
  |}.

  Lemma run_new (limit : U64.t) :
    {{
      M.evaluate (Impl_Gas.run_new limit) 🌲
      Output.Success (new limit)
    }}.
  Proof.
    cbn [evaluate Impl_Gas.run_new].
    eapply Run.Call. {
      apply Impl_MemoryGas.run_new.
    }
    cbn [M.evaluate].
    apply Run.Pure.
  Qed.

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
  Definition new_spent (limit : U64.t) : Self := {|
    Gas.limit := limit;
    Gas.remaining := {| Integer.value := 0 |};
    Gas.refunded := {| Integer.value := 0 |};
    Gas.memory := Impl_MemoryGas.new;
  |}.

  Lemma run_new_spent (limit : U64.t) :
    {{
      M.evaluate (Impl_Gas.run_new_spent limit) 🌲
      Output.Success (new_spent limit)
    }}.
  Proof.
    cbn [evaluate Impl_Gas.run_new_spent].
    eapply Run.Call. {
      apply Impl_MemoryGas.run_new.
    }
    cbn [M.evaluate].
    apply Run.Pure.
  Qed.

  (*
      pub const fn limit(&self) -> u64 {
          self.limit
      }
  *)
  Definition limit (self : Self) : U64.t :=
    self.(Gas.limit).

  Eval cbn [M.evaluate Impl_Gas.run_limit] in fun self => M.evaluate (Impl_Gas.run_limit self).

  (* Lemma run_limit (self : Self) :
    {{
      M.evaluate (Impl_Gas.run_limit self) 🌲
      Output.Success (limit self)
    }}. *)
End Impl_Gas.
