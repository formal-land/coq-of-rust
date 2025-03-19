Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import core.links.clone.
Require core.links.cmp.
Require Import core.links.default.
Require core.links.option.
Require Import core.mem.links.mod.
Require core.mem.mod.
Require Import core.num.links.mod.
Require Import revm_interpreter.gas.calc.
Require Import revm_interpreter.gas.links.calc.
Require Import revm_interpreter.gas.

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

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::gas::MemoryGas").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

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
    Definition get_words_num : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::gas::MemoryGas" "words_num") :=
    {|
      SubPointer.Runner.projection x := Some x.(words_num);
      SubPointer.Runner.injection x y := Some (x <| words_num := y |>);
    |}.

    Lemma get_words_num_is_valid :
      SubPointer.Runner.Valid.t get_words_num.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_words_num_is_valid : run_sub_pointer.

    Definition get_expansion_cost : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::gas::MemoryGas" "expansion_cost") :=
    {|
      SubPointer.Runner.projection x := Some x.(expansion_cost);
      SubPointer.Runner.injection x y := Some (x <| expansion_cost := y |>);
    |}.

    Lemma get_expansion_cost_is_valid :
      SubPointer.Runner.Valid.t get_expansion_cost.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_expansion_cost_is_valid : run_sub_pointer.
  End SubPointer.
End MemoryGas.

Module Impl_Default_for_MemoryGas.
  Definition run_default : Default.Run_default MemoryGas.t.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply gas.Impl_core_default_Default_for_revm_interpreter_gas_MemoryGas.Implements. }
      { reflexivity. }
    }
    { constructor.
      pose (Impl_Default_for_integer.run_default IntegerKind.Usize).
      pose (Impl_Default_for_integer.run_default IntegerKind.U64).
      run_symbolic.
    }
  Defined.

  Instance run : Default.Run MemoryGas.t := {
    Default.default := run_default;
  }.
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
  Instance run_new :
    Run.Trait gas.Impl_revm_interpreter_gas_MemoryGas.new [] [] [] MemoryGas.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.

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
  Instance run_record_new_len
      (self : Ref.t Pointer.Kind.MutRef MemoryGas.t)
      (new_num : Usize.t) :
    Run.Trait
      gas.Impl_revm_interpreter_gas_MemoryGas.record_new_len [] [] [φ self; φ new_num]
      (option U64.t).
  Proof.
    constructor.
    run_symbolic.
  Defined.
End Impl_MemoryGas.

(*
    pub enum MemoryExtensionResult {
        /// Memory was extended.
        Extended,
        /// Memory size stayed the same.
        Same,
        /// Not enough gas to extend memory.s
        OutOfGas,
    }
*)
Module MemoryExtensionResult.
  Inductive t : Set :=
  | Extended
  | Same
  | OutOfGas.

  Global Instance IsLink : Link t := {
    Φ := Ty.path "revm_interpreter::gas::MemoryExtensionResult";
    φ x :=
      match x with
      | Extended => Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Extended" []
      | Same => Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Same" []
      | OutOfGas => Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::OutOfGas" []
      end;
  }.

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::gas::MemoryExtensionResult").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with_Extended :
    Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Extended" [] = φ Extended.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Extended : of_value.

  Lemma of_value_with_Same :
    Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Same" [] = φ Same.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_Same : of_value.

  Lemma of_value_with_OutOfGas :
    Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::OutOfGas" [] = φ OutOfGas.
  Proof. reflexivity. Qed.
  Smpl Add apply of_value_with_OutOfGas : of_value.

  Definition of_value_Extended :
    OfValue.t (Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Extended" []).
  Proof. econstructor; apply of_value_with_Extended. Defined.
  Smpl Add apply of_value_Extended : of_value.

  Definition of_value_Same :
    OfValue.t (Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::Same" []).
  Proof. econstructor; apply of_value_with_Same. Defined.
  Smpl Add apply of_value_Same : of_value.

  Definition of_value_OutOfGas :
    OfValue.t (Value.StructTuple "revm_interpreter::gas::MemoryExtensionResult::OutOfGas" []).
  Proof. econstructor; apply of_value_with_OutOfGas. Defined.
  Smpl Add apply of_value_OutOfGas : of_value.
End MemoryExtensionResult.

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

  Definition of_ty : OfTy.t (Ty.path "revm_interpreter::gas::Gas").
  Proof. eapply OfTy.Make with (A := t); reflexivity. Defined.
  Smpl Add apply of_ty : of_ty.

  Lemma of_value_with limit limit' remaining remaining' refunded refunded' memory memory' :
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
  Smpl Add apply of_value_with : of_value.

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
  Proof. econstructor; apply of_value_with; eassumption. Defined.
  Smpl Add apply of_value : of_value.

  Module SubPointer.
    Definition get_limit : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "limit") :=
    {|
      SubPointer.Runner.projection x := Some x.(limit);
      SubPointer.Runner.injection x y := Some (x <| limit := y |>);
    |}.

    Lemma get_limit_is_valid :
      SubPointer.Runner.Valid.t get_limit.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_limit_is_valid : run_sub_pointer.

    Definition get_remaining : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "remaining") :=
    {|
      SubPointer.Runner.projection x := Some x.(remaining);
      SubPointer.Runner.injection x y := Some (x <| remaining := y |>);
    |}.

    Lemma get_remaining_is_valid :
      SubPointer.Runner.Valid.t get_remaining.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_remaining_is_valid : run_sub_pointer.

    Definition get_refunded : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "refunded") :=
    {|
      SubPointer.Runner.projection x := Some x.(refunded);
      SubPointer.Runner.injection x y := Some (x <| refunded := y |>);
    |}.

    Lemma get_refunded_is_valid :
      SubPointer.Runner.Valid.t get_refunded.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_refunded_is_valid : run_sub_pointer.

    Definition get_memory : SubPointer.Runner.t t
      (Pointer.Index.StructRecord "revm_interpreter::gas::Gas" "memory") :=
    {|
      SubPointer.Runner.projection x := Some x.(memory);
      SubPointer.Runner.injection x y := Some (x <| memory := y |>);
    |}.

    Lemma get_memory_is_valid :
      SubPointer.Runner.Valid.t get_memory.
    Proof.
      now constructor.
    Qed.
    Smpl Add apply get_memory_is_valid : run_sub_pointer.
  End SubPointer.
End Gas.

Module Impl_Clone_for_Gas.
  Definition run_clone : Clone.Run_clone Gas.t.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply gas.Impl_core_clone_Clone_for_revm_interpreter_gas_Gas.Implements. }
      { reflexivity. }
    }
    { constructor.
      run_symbolic.
    }
  Defined.

  Instance run : clone.Clone.Run Gas.t := {
    Clone.clone := run_clone;
  }.
End Impl_Clone_for_Gas.

Module Impl_Default_for_Gas.
  Definition run_default : Default.Run_default Gas.t.
  Proof.
    eexists.
    { eapply IsTraitMethod.Defined.
      { apply gas.Impl_core_default_Default_for_revm_interpreter_gas_Gas.Implements. }
      { reflexivity. }
    }
    { constructor.
      pose (default.Impl_Default_for_integer.run_default IntegerKind.U64).
      pose (default.Impl_Default_for_integer.run_default IntegerKind.I64).
      pose Impl_Default_for_MemoryGas.run_default.
      run_symbolic.
    }
  Defined.

  Instance run : Default.Run Gas.t := {
    Default.default := run_default;
  }.
End Impl_Default_for_Gas.

Module Impl_Gas.
  Import Impl_MemoryGas.
  Import Impl_u64.

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
  Instance run_new (limit : U64.t) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.new [] [] [φ limit] Self.
  Proof.
    constructor.
    run_symbolic.
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
  Instance run_new_spent (limit : U64.t) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.new_spent [] [] [φ limit] Self.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub const fn limit(&self) -> u64 {
          self.limit
      }
  *)
  Instance run_limit (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.limit [] [] [φ self] U64.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub const fn memory(&self) -> u64 {
          0
      }
  *)
  Instance run_memory (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.memory [] [] [φ self] U64.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub const fn refunded(&self) -> i64 {
          self.refunded
      }
  *)
  Instance run_refunded (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.refunded [] [] [φ self] I64.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub const fn spent(&self) -> u64 {
          self.limit - self.remaining
      }
  *)
  Instance run_spent (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.spent [] [] [φ self] U64.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub const fn remaining(&self) -> u64 {
          self.remaining
      }
  *)
  Instance run_remaining (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.remaining [] [] [φ self] U64.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub const fn remaining_63_of_64_parts(&self) -> u64 {
          self.remaining - self.remaining / 64
      }
  *)
  Instance run_remaining_63_of_64_parts (self : Ref.t Pointer.Kind.Ref Self) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.remaining_63_of_64_parts [] [] [φ self] U64.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub fn erase_cost(&mut self, returned: u64) {
          self.remaining += returned;
      }
  *)
  Instance run_erase_cost (self : Ref.t Pointer.Kind.Ref Self) (returned : U64.t) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.erase_cost [] [] [φ self; φ returned] unit.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub fn spend_all(&mut self) {
          self.remaining = 0;
      }
  *)
  Instance run_spend_all (self : Ref.t Pointer.Kind.MutRef Self) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.spend_all [] [] [φ self] unit.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub fn record_refund(&mut self, refund: i64) {
          self.refunded += refund;
      }
  *)
  Instance run_record_refund (self : Ref.t Pointer.Kind.MutRef Self) (refund : I64.t) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.record_refund [] [] [φ self; φ refund] unit.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub fn set_final_refund(&mut self, is_london: bool) {
          let max_refund_quotient = if is_london { 5 } else { 2 };
          self.refunded = (self.refunded() as u64).min(self.spent() / max_refund_quotient) as i64;
      }
  *)
  Instance run_set_final_refund (self : Ref.t Pointer.Kind.MutRef Self) (is_london : bool) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.set_final_refund [] [] [φ self; φ is_london] unit.
  Proof.
    constructor.
    pose cmp.Impl_Ord_for_u64.run_min.
    run_symbolic.
  Defined.

  (*
      pub fn set_refund(&mut self, refund: i64) {
          self.refunded = refund;
      }
  *)
  Instance run_set_refund (self : Ref.t Pointer.Kind.MutRef Self) (refund : I64.t) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.set_refund [] [] [φ self; φ refund] unit.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub fn record_cost(&mut self, cost: u64) -> bool {
        let (remaining, overflow) = self.remaining.overflowing_sub(cost);
        let success = !overflow;
        if success {
            self.remaining = remaining;
        }
        success
    }
  *)
  Instance run_record_cost (self : Ref.t Pointer.Kind.MutRef Self) (cost : U64.t) :
    Run.Trait gas.Impl_revm_interpreter_gas_Gas.record_cost [] [] [φ self; φ cost] bool.
  Proof.
    constructor.
    run_symbolic.
  Defined.

  (*
      pub fn record_memory_expansion(&mut self, new_len: usize) -> MemoryExtensionResult {
          let Some(additional_cost) = self.memory.record_new_len(new_len) else {
              return MemoryExtensionResult::Same;
          };

          if !self.record_cost(additional_cost) {
              return MemoryExtensionResult::OutOfGas;
          }

          MemoryExtensionResult::Extended
      }
  *)
  Instance run_record_memory_expansion
      (self : Ref.t Pointer.Kind.MutRef Self)
      (new_len : Usize.t) :
    Run.Trait
      gas.Impl_revm_interpreter_gas_Gas.record_memory_expansion [] [] [φ self; φ new_len]
      MemoryExtensionResult.t.
  Proof.
    constructor.
    run_symbolic.
  Defined.
End Impl_Gas.
