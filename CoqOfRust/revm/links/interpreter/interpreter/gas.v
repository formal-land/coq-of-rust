Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require core.links.clone.
Require core.links.cmp.
Require core.links.default.
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
      eapply Run.CallPrimitiveGetTraitMethod. {
        apply H_default_usize.
      }
      eapply Run.CallClosure. {
        apply run_default_usize.
      }
      intros []; cbn; [|run_panic].
      eapply Run.CallPrimitiveGetTraitMethod. {
        apply H_default_u64.
      }
      eapply Run.CallClosure. {
        apply run_default_u64.
      }
      intros []; cbn; [|run_panic].
      run_symbolic;
        try apply Output.Success;
        try apply MemoryGas.Build_t;
        try with_strategy transparent [φ] reflexivity.
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
    run_symbolic;
      try apply Output.Success;
      try apply MemoryGas.Build_t;
      try apply Integer.Build_t;
      try with_strategy transparent [φ] reflexivity.
  Defined.
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
  End SubPointer.
End Gas.

Module Impl_Clone.
  Definition run_clone : clone.Clone.Run_clone Gas.t.
  Proof.
    eexists; split.
    { eapply IsTraitMethod.Defined.
      { apply gas.Impl_core_clone_Clone_for_revm_interpreter_gas_Gas.Implements. }
      { reflexivity. }
    }
    { intros.
      run_symbolic;
        try apply Output.Success;
        try reflexivity.
    }
  Defined.

  Definition run : clone.Clone.Run Gas.t.
  Proof.
    constructor.
    { (* clone *)
      exact run_clone.
    }
  Defined.
End Impl_Clone.

Module Impl_Default.
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
      destruct (Impl_Default_for_MemoryGas.run_default)
        as [default_memory_gas [H_default_memory_gas run_default_memory_gas]].
      eapply Run.CallPrimitiveGetTraitMethod. {
        apply H_default_u64.
      }
      eapply Run.CallClosure. {
        apply run_default_u64.
      }
      intros []; cbn; [|run_panic].
      eapply Run.CallPrimitiveGetTraitMethod. {
        apply H_default_u64.
      }
      eapply Run.CallClosure. {
        apply run_default_u64.
      }
      intros []; cbn; [|run_panic].
      eapply Run.CallPrimitiveGetTraitMethod. {
        apply H_default_i64.
      }
      eapply Run.CallClosure. {
        apply run_default_i64.
      }
      intros []; cbn; [|run_panic].
      eapply Run.CallPrimitiveGetTraitMethod. {
        apply H_default_memory_gas.
      }
      eapply Run.CallClosure. {
        apply run_default_memory_gas.
      }
      intros []; cbn; [|run_panic].
      run_symbolic;
        try apply Output.Success;
        try apply Gas.Build_t;
        try with_strategy transparent [φ] reflexivity.
    }
  Defined.

  Definition run : default.Default.Run Gas.t.
  Proof.
    constructor.
    { (* default *)
      exact run_default.
    }
  Defined.
End Impl_Default.

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
    eapply CallPrimitiveGetAssociatedFunction. {
      apply gas.Impl_revm_interpreter_gas_MemoryGas.AssociatedFunction_new.
    }
    eapply Run.CallClosure. {
      apply Impl_MemoryGas.run_new.
    }
    intros []; cbn; [|run_panic].
    run_symbolic;
      try apply Output.Success;
      try simple apply Gas.Build_t;
      try apply Integer.Build_t;
      try with_strategy transparent [φ] reflexivity.
  Defined.

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
    eapply CallPrimitiveGetAssociatedFunction. {
      apply gas.Impl_revm_interpreter_gas_MemoryGas.AssociatedFunction_new.
    }
    eapply Run.CallClosure. {
      apply Impl_MemoryGas.run_new.
    }
    intros []; cbn; [|run_panic].
    run_symbolic;
      try apply Output.Success;
      try simple apply Gas.Build_t;
      try apply Integer.Build_t;
      try with_strategy transparent [φ] reflexivity.
  Defined.

  (*
      pub const fn limit(&self) -> u64 {
          self.limit
      }
  *)
  Definition run_limit (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.limit [] [] [φ self] 🔽 U64.t }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_limit_is_valid.
    run_symbolic;
      try apply Output.Success;
      try reflexivity.
  Defined.

  (*
      pub const fn memory(&self) -> u64 {
          0
      }
  *)
  Definition run_memory (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.memory [] [] [φ self] 🔽 U64.t }}.
  Proof.
    run_symbolic;
      try apply Output.Success;
      try apply Integer.Build_t;
      try with_strategy transparent [φ] reflexivity.
  Defined.

  (*
      pub const fn refunded(&self) -> i64 {
          self.refunded
      }
  *)
  Definition run_refunded (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.refunded [] [] [φ self] 🔽 I64.t }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_refunded_is_valid.
    run_symbolic;
      try apply Output.Success;
      try reflexivity.
  Defined.

  (*
      pub const fn spent(&self) -> u64 {
          self.limit - self.remaining
      }
  *)
  Definition run_spent (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.spent [] [] [φ self] 🔽 U64.t }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_limit_is_valid.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_remaining_is_valid.
    run_symbolic;
      try apply Output.Success;
      try apply Integer.Build_t;
      try with_strategy transparent [φ] reflexivity.
  Defined.

  (*
      pub const fn remaining(&self) -> u64 {
          self.remaining
      }
  *)
  Definition run_remaining (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.remaining [] [] [φ self] 🔽 U64.t }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_remaining_is_valid.
    run_symbolic;
      try apply Output.Success;
      try reflexivity.
  Defined.

  (*
      pub const fn remaining_63_of_64_parts(&self) -> u64 {
          self.remaining - self.remaining / 64
      }
  *)
  Definition run_remaining_63_of_64_parts (self : Ref.t Pointer.Kind.Ref Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.remaining_63_of_64_parts [] [] [φ self] 🔽 U64.t }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_remaining_is_valid.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_remaining_is_valid.
    run_symbolic;
      try apply Output.Success;
      try apply Integer.Build_t;
      try with_strategy transparent [φ] reflexivity.
  Defined.

  (*
      pub fn erase_cost(&mut self, returned: u64) {
          self.remaining += returned;
      }
  *)
  Definition run_erase_cost (self : Ref.t Pointer.Kind.Ref Self) (returned : U64.t) :
    {{ gas.Impl_revm_interpreter_gas_Gas.erase_cost [] [] [φ self; φ returned] 🔽 unit }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_remaining_is_valid.
    run_symbolic.
    cbn.
    unshelve eapply Run.CallPrimitiveStateWrite;
      try apply Integer.Build_t;
      try with_strategy transparent [φ] reflexivity.
    eapply Run.Let. {
      run_symbolic.
    }
    intros; run_symbolic;
      try apply Output.Success;
      try reflexivity.
  Defined.

  (*
      pub fn spend_all(&mut self) {
          self.remaining = 0;
      }
  *)
  Definition run_spend_all (self : Ref.t Pointer.Kind.MutRef Self) :
    {{ gas.Impl_revm_interpreter_gas_Gas.spend_all [] [] [φ self] 🔽 unit }}.
  Proof.
    run_symbolic.
    eapply Run.Let. {
      run_symbolic.
      run_sub_pointer Gas.SubPointer.get_remaining_is_valid.
      unshelve eapply Run.CallPrimitiveStateWrite;
        try apply Integer.Build_t;
        try with_strategy transparent [φ] reflexivity.
      run_symbolic.
    }
    intros; run_symbolic;
      try apply Output.Success;
      try reflexivity.
  Defined.

  (*
      pub fn record_refund(&mut self, refund: i64) {
          self.refunded += refund;
      }
  *)
  Definition run_record_refund (self : Ref.t Pointer.Kind.MutRef Self) (refund : I64.t) :
    {{ gas.Impl_revm_interpreter_gas_Gas.record_refund [] [] [φ self; φ refund] 🔽 unit }}.
  Proof.
    run_symbolic.
    run_sub_pointer Gas.SubPointer.get_refunded_is_valid.
    run_symbolic.
    unshelve eapply Run.CallPrimitiveStateWrite;
      try apply Integer.Build_t;
      try with_strategy transparent [φ] reflexivity.
    eapply Run.Let. {
      run_symbolic.
    }
    intros; run_symbolic;
      try apply Output.Success;
      try reflexivity.
  Defined.

  (*
  (*
      pub fn set_final_refund(&mut self, is_london: bool) {
          let max_refund_quotient = if is_london { 5 } else { 2 };
          self.refunded = (self.refunded() as u64).min(self.spent() / max_refund_quotient) as i64;
      }
  *)
  Definition run_set_final_refund (self : Ref.t Pointer.Kind.MutRef Self) (is_london : bool) :
    {{ gas.Impl_revm_interpreter_gas_Gas.set_final_refund [] [] [φ self; φ is_london] 🔽 unit }}.
  Proof.
    run_symbolic.
    eapply Run.Let with (output_to_value' := fun (v : Ref.t Pointer.Kind.Ref U64.t) => inl (φ v)). {
      run_symbolic.
      eapply Run.CallPrimitiveAreEqual with (A := bool); try reflexivity.
      intros []; cbn.
      { unshelve eapply CallPrimitiveStateAllocImmediate with (A := U64.t);
          try apply Integer.Build_t;
          try exact Pointer.Kind.Ref;
          try reflexivity.
        run_symbolic.
      }
      { unshelve eapply CallPrimitiveStateAllocImmediate with (A := U64.t);
          try apply Integer.Build_t;
          try exact Pointer.Kind.Ref;
          try reflexivity.
        run_symbolic.
      }
    }
    intros.
    eapply Run.Let. {
      run_symbolic.
      run_sub_pointer Gas.SubPointer.get_refunded_is_valid.
      destruct cmp.Impl_Ord_for_u64.run_min as [min [H_min run_min]].
      eapply Run.CallPrimitiveGetTraitMethod. {
        apply H_min.
      }
      eapply Run.CallPrimitiveGetAssociatedFunction. {
        apply gas.Impl_revm_interpreter_gas_Gas.AssociatedFunction_refunded.
      }
      run_symbolic.
      eapply Run.CallClosure. {
        pose proof (run_refunded self).
      }
    }
    intros; run_symbolic.
    run_sub_pointer Gas.SubPointer.get_refunded_is_valid.
    run_symbolic.
    eapply Run.Let. {
      run_symbolic.
    }
    intros; run_symbolic.
    eapply Run.Let. {
      run_symbolic.
    }
    intros; run_symbolic.
  *)
End Impl_revm_interpreter_gas_Gas.
