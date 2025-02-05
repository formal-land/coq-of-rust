Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.lib.
Require Import CoqOfRust.links.M.
Require core.links.clone.
Require core.links.cmp.
Require core.links.default.
Require core.links.option.
Require Import revm.translations.interpreter.gas.

Import Run.

(*
pub struct MemoryGas {
    /// Current memory length
    pub words_num: usize,
    /// Current memory expansion cost
    pub expansion_cost: u64,
}
*)
Module MemoryGas.
  Record t : Set := {
    words_num : Usize.t;
    expansion_cost : U64.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::gas::MemoryGas";
    φ x :=
      Value.StructRecord "revm_interpreter::gas::MemoryGas" [
        ("words_num", φ x.(words_num));
        ("expansion_cost", φ x.(expansion_cost))
      ];
  }.

  Lemma of_value_with words_num words_num' expansion_cost expansion_cost' :
    words_num' = φ words_num ->
    expansion_cost' = φ expansion_cost ->
    Value.StructRecord "revm_interpreter::gas::MemoryGas" [
      ("words_num", words_num');
      ("expansion_cost", expansion_cost')
    ] = φ (Build_t words_num expansion_cost).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_with : of_value.

  Definition of_value (words_num : Usize.t) words_num' (expansion_cost : U64.t) expansion_cost' :
    words_num' = φ words_num ->
    expansion_cost' = φ expansion_cost ->
    OfValue.t (
      Value.StructRecord "revm_interpreter::gas::MemoryGas" [
        ("words_num", words_num');
        ("expansion_cost", expansion_cost')
      ]
    ).
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add apply of_value : of_value.

  Module SubPointer.
    Definition get_words_num : SubPointer.Runner.t t Usize.t := {|
      SubPointer.Runner.index :=
        Pointer.Index.StructRecord "revm_interpreter::gas::MemoryGas" "words_num";
      SubPointer.Runner.projection x := Some x.(words_num);
      SubPointer.Runner.injection x y := Some (x <| words_num := y |>);
    |}.

    Lemma get_words_num_is_valid :
      SubPointer.Runner.Valid.t get_words_num.
    Proof.
      now constructor.
    Qed.
    Smpl Add run_sub_pointer get_words_num_is_valid : run_symbolic.

    Definition get_expansion_cost : SubPointer.Runner.t t U64.t := {|
      SubPointer.Runner.index :=
        Pointer.Index.StructRecord "revm_interpreter::gas::MemoryGas" "expansion_cost";
      SubPointer.Runner.projection x := Some x.(expansion_cost);
      SubPointer.Runner.injection x y := Some (x <| expansion_cost := y |>);
    |}.

    Lemma get_expansion_cost_is_valid :
      SubPointer.Runner.Valid.t get_expansion_cost.
    Proof.
      now constructor.
    Qed.
    Smpl Add run_sub_pointer get_expansion_cost_is_valid : run_symbolic.
  End SubPointer.
End MemoryGas.

Module Impl_Default_for_MemoryGas.
  Definition run_default : default.Default.Run_default MemoryGas.t.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Defined.
      { apply gas.Impl_core_default_Default_for_revm_interpreter_gas_MemoryGas.Implements. }
      { reflexivity. }
    }
    { intros; cbn.
      destruct (default.Impl_Default_for_integer.run_default IntegerKind.Usize)
        as [default_usize [H_default_usize run_default_usize]].
      destruct (default.Impl_Default_for_integer.run_default IntegerKind.U64)
        as [default_u64 [H_default_u64 run_default_u64]].
      run_symbolic.
    }
  Defined.

  Definition run : default.Default.Run MemoryGas.t.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_MemoryGas.

Module Impl_MemoryGas.
  Definition Self : Set := MemoryGas.t.

  (*
  pub const fn new() -> Self {
      Self {
          words_num: 0,
          expansion_cost: 0,
      }
  }
  *)
  Definition run_new : {{ gas.Impl_revm_interpreter_gas_MemoryGas.new [] [] [] 🔽 MemoryGas.t }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_new : run_closure.

  (*
  pub fn record_new_len(&mut self, new_num: usize) -> Option<u64> {
      if new_num <= self.words_num {
          return None;
      }
      self.words_num = new_num;
      let mut cost = crate::gas::calc::memory_gas(new_num);
      core::mem::swap(&mut self.expansion_cost, &mut cost);
      // Safe to subtract because we know that new_len > length
      // Notice the swap above.
      Some(self.expansion_cost - cost)
  }
  *)
  Definition run_record_new_len
      (self : Ref.t Pointer.Kind.MutRef MemoryGas.t)
      (new_num : Usize.t) :
    {{
      gas.Impl_revm_interpreter_gas_MemoryGas.record_new_len [] [] [φ self; φ new_num] 🔽
      option U64.t
    }}.
  Proof.
    run_symbolic.
    eapply Run.Let. {
      run_symbolic.
      eapply Run.CallPrimitiveAreEqual with (A := bool); try smpl of_value.
      intros []; run_symbolic.
    }
    intros [|[]]; run_symbolic.
    eapply Run.Let. {
      admit.
    }
    admit.
  Admitted.
  Smpl Add apply run_record_new_len : run_closure.
End Impl_MemoryGas.

(*
  /// Represents the state of gas during execution.
  #[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
  #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
  pub struct Gas {
      /// The initial gas limit. This is constant throughout execution.
      limit: u64,
      /// The remaining gas.
      remaining: u64,
      /// Refunded gas. This is used only at the end of execution.
      refunded: i64,
      /// Memoisation of values for memory expansion cost.
      memory: MemoryGas,
  }
*)

Module Gas.
  Record t : Set := {
    limit : U64.t;
    remaining : U64.t;
    refunded : I64.t;
    memory : MemoryGas.t;
  }.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::gas::Gas";
    φ x :=
      Value.StructRecord "revm_interpreter::gas::Gas" [
        ("limit", φ x.(limit));
        ("remaining", φ x.(remaining));
        ("refunded", φ x.(refunded));
        ("memory", φ x.(memory))
      ];
  }.

  Lemma of_value_impl limit limit' remaining remaining' refunded refunded' memory memory' :
    limit' = φ limit ->
    remaining' = φ remaining ->
    refunded' = φ refunded ->
    memory' = φ memory ->
    Value.StructRecord "revm_interpreter::gas::Gas" [
      ("limit", limit');
      ("remaining", remaining');
      ("refunded", refunded');
      ("memory", memory')
    ] = φ (Build_t limit remaining refunded memory).
  Proof. now intros; subst. Qed.
  Smpl Add apply of_value_impl : of_value.

  Definition of_value
      (limit : U64.t) limit'
      (remaining : U64.t) remaining'
      (refunded : I64.t) refunded'
      (memory : MemoryGas.t) memory' :
    limit' = φ limit ->
    remaining' = φ remaining ->
    refunded' = φ refunded ->
    memory' = φ memory ->
    OfValue.t (
      Value.StructRecord "revm_interpreter::gas::Gas" [
        ("limit", limit');
        ("remaining", remaining');
        ("refunded", refunded');
        ("memory", memory')
      ]
    ).
  Proof. econstructor; apply of_value_impl; eassumption. Defined.
  Smpl Add apply of_value : of_value.

  Module SubPointer.
    Definition get_limit : SubPointer.Runner.t t U64.t := {|
      SubPointer.Runner.index :=
        Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "limit";
      SubPointer.Runner.projection x := Some x.(limit);
      SubPointer.Runner.injection x y := Some (x <| limit := y |>);
    |}.

    Lemma get_limit_is_valid :
      SubPointer.Runner.Valid.t get_limit.
    Proof.
      now constructor.
    Qed.
    Smpl Add run_sub_pointer get_limit_is_valid : run_symbolic.

    Definition get_remaining : SubPointer.Runner.t t U64.t := {|
      SubPointer.Runner.index :=
        Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "remaining";
      SubPointer.Runner.projection x := Some x.(remaining);
      SubPointer.Runner.injection x y := Some (x <| remaining := y |>);
    |}.

    Lemma get_remaining_is_valid :
      SubPointer.Runner.Valid.t get_remaining.
    Proof.
      now constructor.
    Qed.
    Smpl Add run_sub_pointer get_remaining_is_valid : run_symbolic.

    Definition get_refunded : SubPointer.Runner.t t I64.t := {|
      SubPointer.Runner.index :=
        Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "refunded";
      SubPointer.Runner.projection x := Some x.(refunded);
      SubPointer.Runner.injection x y := Some (x <| refunded := y |>);
    |}.

    Lemma get_refunded_is_valid :
      SubPointer.Runner.Valid.t get_refunded.
    Proof.
      now constructor.
    Qed.
    Smpl Add run_sub_pointer get_refunded_is_valid : run_symbolic.

    Definition get_memory : SubPointer.Runner.t t MemoryGas.t := {|
      SubPointer.Runner.index :=
        Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "memory";
      SubPointer.Runner.projection x := Some x.(memory);
      SubPointer.Runner.injection x y := Some (x <| memory := y |>);
    |}.

    Lemma get_memory_is_valid :
      SubPointer.Runner.Valid.t get_memory.
    Proof.
      now constructor.
    Qed.
    Smpl Add run_sub_pointer get_memory_is_valid : run_symbolic.
  End SubPointer.
End Gas.

Module Impl_Clone_for_Gas.
  Definition run_clone : clone.Clone.Run_clone Gas.t.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Defined.
      { apply gas.Impl_core_clone_Clone_for_revm_interpreter_gas_Gas.Implements. }
      { reflexivity. }
    }
    { intros.
      run_symbolic.
    }
  Defined.

  Definition run : clone.Clone.Run Gas.t.
  Proof.
    constructor.
    { (* clone *)
      exact run_clone.
    }
  Defined.
End Impl_Clone_for_Gas.

Module Impl_Default_for_Gas.
  Definition run_default : default.Default.Run_default Gas.t.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Defined.
      { apply gas.Impl_core_default_Default_for_revm_interpreter_gas_Gas.Implements. }
      { reflexivity. }
    }
    { intros; cbn.
      destruct (default.Impl_Default_for_integer.run_default IntegerKind.U64)
        as [default_u64 [H_default_u64 run_default_u64]].
      destruct (default.Impl_Default_for_integer.run_default IntegerKind.I64)
        as [default_i64 [H_default_i64 run_default_i64]].
      destruct Impl_Default_for_MemoryGas.run_default
        as [default_memory_gas [H_default_memory_gas run_default_memory_gas]].
      eapply Run.CallPrimitiveGetTraitMethod. {
        apply H_default_u64.
      }
      run_symbolic.
    }
  Defined.

  Definition run : default.Default.Run Gas.t.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default_for_Gas.

Module Impl_revm_interpreter_gas_Gas.
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
  Definition run_new (limit : U64.t) :
    {{ gas.Impl_revm_interpreter_gas_Gas.new [] [] [φ limit] 🔽 Self }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_new : run_closure.

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
    {{ gas.Impl_revm_interpreter_gas_Gas.new_spent [] [] [φ limit] 🔽 Self }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_new_spent : run_closure.

  (*
      pub const fn limit(&self) -> u64 {
          self.limit
      }
  *)
  Definition run_limit (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.limit [] [] [φ self] 🔽 U64.t }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_limit : run_closure.

  (*
      pub const fn memory(&self) -> u64 {
          0
      }
  *)
  Definition run_memory (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.memory [] [] [φ self] 🔽 U64.t }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_memory : run_closure.


  (*
      pub const fn refunded(&self) -> i64 {
          self.refunded
      }
  *)
  Definition run_refunded (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.refunded [] [] [φ self] 🔽 I64.t }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_refunded : run_closure.

  (*
      pub const fn spent(&self) -> u64 {
          self.limit - self.remaining
      }
  *)
  Definition run_spent (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.spent [] [] [φ self] 🔽 U64.t }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_spent : run_closure.

  (*
      pub const fn remaining(&self) -> u64 {
          self.remaining
      }
  *)
  Definition run_remaining (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.remaining [] [] [φ self] 🔽 U64.t }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_remaining : run_closure.


  (*
      pub const fn remaining_63_of_64_parts(&self) -> u64 {
          self.remaining - self.remaining / 64
      }
  *)
  Definition run_remaining_63_of_64_parts (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.remaining_63_of_64_parts [] [] [φ self] 🔽 U64.t }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_remaining_63_of_64_parts : run_closure.

  (*
      pub fn erase_cost(&mut self, returned: u64) {
          self.remaining += returned;
      }
  *)
  Definition run_erase_cost (self : Ref.t Pointer.Kind.Ref Self) (returned : U64.t) :
    {{ gas.Impl_revm_interpreter_gas_Gas.erase_cost [] [] [φ self; φ returned] 🔽 unit }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_erase_cost : run_closure.


  (*
      pub fn spend_all(&mut self) {
          self.remaining = 0;
      }
  *)
  Definition run_spend_all (self : Ref.t Pointer.Kind.MutRef Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.spend_all [] [] [φ self] 🔽 unit }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_spend_all : run_closure.

  (*
      pub fn record_refund(&mut self, refund: i64) {
          self.refunded += refund;
      }
  *)
  Definition run_record_refund (self : Ref.t Pointer.Kind.MutRef Self) (refund : I64.t) :
    {{ gas.Impl_revm_interpreter_gas_Gas.record_refund [] [] [φ self; φ refund] 🔽 unit }}.
  Proof.
    run_symbolic.
  Defined.
  Smpl Add apply run_record_refund : run_closure.

  (*
      pub fn set_final_refund(&mut self, is_london: bool) {
          let max_refund_quotient = if is_london { 5 } else { 2 };
          self.refunded = (self.refunded() as u64).min(self.spent() / max_refund_quotient) as i64;
      }
  *)
  Definition run_set_final_refund (self : Ref.t Pointer.Kind.MutRef Self) (is_london : bool) :
    {{ gas.Impl_revm_interpreter_gas_Gas.set_final_refund [] [] [φ self; φ is_london] 🔽 unit }}.
  Proof.
    destruct cmp.Impl_Ord_for_u64.run_min as [min [H_min run_min]].
    run_symbolic.
    eapply Run.Let. {
      run_symbolic.
      eapply Run.CallPrimitiveAreEqual with (A := bool); try reflexivity.
      intros []; run_symbolic.
    }
    cbn; intros []; run_symbolic.
  Defined.
End Impl_revm_interpreter_gas_Gas.
