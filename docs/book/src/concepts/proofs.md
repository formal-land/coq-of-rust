# Proofs: Verification

This chapter covers writing proofs about Rust programs using rocq-of-rust.

## Proof Architecture

The rocq-of-rust verification workflow:

```
┌─────────────┐    ┌─────────────┐    ┌─────────────┐
│   Linked    │    │ Simulation  │    │  Property   │
│    Code     │ ═══│   Equiv.    │═══▶│   Proofs    │
│             │    │   Proof     │    │             │
└─────────────┘    └─────────────┘    └─────────────┘
       ▲                                     │
       │                                     │
       └──────── Correctness Chain ──────────┘
```

1. **Linked code** faithfully represents Rust semantics
2. **Equivalence proofs** show simulations match linked code
3. **Property proofs** use simulations for ergonomic reasoning
4. **Correctness chain** transfers properties to original Rust

## Types of Properties

### Functional Correctness

Prove functions compute expected results:

```rocq
Lemma factorial_correct : forall n,
  factorial n = fact_spec n.
```

### Safety Properties

Prove absence of runtime errors:

```rocq
Lemma no_overflow : forall a b,
  a + b <= MAX_U64 ->
  add_checked a b = Some (a + b).
```

### Invariant Preservation

Prove data structure invariants are maintained:

```rocq
Lemma push_preserves_sorted : forall x s,
  sorted s ->
  x >= max_element s ->
  sorted (push x s).
```

## Proof Strategies

### Direct Computation

For simple properties, `vm_compute` and `reflexivity` suffice:

```rocq
Goal op_add 2 3 = 5.
Proof. vm_compute. reflexivity. Qed.
```

### Structural Induction

For recursive functions, induct on the structure:

```rocq
Lemma list_length_app : forall {A} (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  induction l1 as [|h t IH].
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.
```

### Case Analysis

When behavior depends on conditions:

```rocq
Lemma cmp_trichotomy : forall a b,
  a < b \/ a = b \/ a > b.
Proof.
  intros. destruct (Z.compare a b) eqn:E.
  - right. left. lia.
  - left. lia.
  - right. right. lia.
Qed.
```

### Automation

Use tactics like `lia`, `auto`, `omega` for arithmetic:

```rocq
Lemma bounded_add : forall a b,
  0 <= a -> 0 <= b ->
  a + b >= a.
Proof. intros. lia. Qed.
```

## Working with Simulations

### State Manipulation

Simulations often use record updates:

```rocq
Lemma gas_decreases : forall interp cost,
  cost <= interp.(Interpreter.gas) ->
  (interp <| Interpreter.gas := interp.(Interpreter.gas) - cost |>)
    .(Interpreter.gas) = interp.(Interpreter.gas) - cost.
Proof. reflexivity. Qed.
```

### Stack Properties

Prove stack operations are correct:

```rocq
Lemma pop_push_inverse : forall s v,
  pop (push s v) = Some (v, s).
Proof.
  intros. unfold push, pop. simpl. reflexivity.
Qed.
```

## EVM Verification Example

Complete example proving LT opcode correctness:

### Property Specification

```rocq
(** LT returns 1 if first operand < second, else 0 *)
Definition lt_spec (a b : Z) : Z :=
  if a <? b then 1 else 0.
```

### Equivalence to Simulation

```rocq
Lemma op_lt_correct : forall a b interpreter,
  let stack := {| Stack.value := [
    {| Uint.value := a |};
    {| Uint.value := b |}
  ] |} in
  let interp := interpreter <| Interpreter.stack := stack |> in
  has_enough_gas interp ->
  (op_lt interp).(Interpreter.stack).(Stack.value) =
    [{| Uint.value := lt_spec a b |}].
Proof.
  intros.
  unfold op_lt, lt_spec.
  (* Unfold macros and simplify *)
  (* ... *)
Qed.
```

### Integration Tests

```rocq
(** Concrete test cases *)
Goal lt_spec 5 10 = 1. Proof. reflexivity. Qed.
Goal lt_spec 10 5 = 0. Proof. reflexivity. Qed.
Goal lt_spec 5 5 = 0. Proof. reflexivity. Qed.
```

## Composing Proofs

For multi-step operations, compose smaller lemmas:

```rocq
Lemma execute_sequence : forall interp ops,
  execute_all interp ops =
  fold_left execute interp ops.

Lemma sequence_gas_consumption : forall interp ops,
  total_gas_used (execute_all interp ops) =
  sum (map op_gas_cost ops).
```

## Dealing with Complexity

### Modularize

Break proofs into smaller lemmas:

```rocq
(* Helper lemmas *)
Lemma helper1 : ... Proof. ... Qed.
Lemma helper2 : ... Proof. ... Qed.

(* Main theorem uses helpers *)
Theorem main : ...
Proof. apply helper1. apply helper2. Qed.
```

### Use Automation

Define custom tactics for repetitive patterns:

```rocq
Ltac solve_gas :=
  unfold gas_macro;
  destruct (gas_check _);
  try reflexivity;
  try lia.
```

### Admit Temporarily

During development, admit subgoals to focus on structure:

```rocq
Lemma work_in_progress : ...
Proof.
  step1.
  - subgoal1. (* TODO *)
    admit.
  - subgoal2.
    apply lemma.
Admitted. (* Change to Qed when complete *)
```

## Common Issues

### Proof Timeouts

If proofs run slowly:
- Avoid unfolding too much at once
- Use `vm_compute` for concrete calculations
- Make simulations more direct

### Unification Failures

When tactics fail to match:
- Check types with `Check` command
- Use `@` to make implicit arguments explicit
- Try `change` tactic to rewrite goals

### Missing Lemmas

When needed facts aren't available:
- Search with `Search` command
- Check standard library (`Require Import Lia. Search Z.`)
- Prove as helper lemma if novel

## Best Practices

1. **Write specifications first** - Define what correct means before proving
2. **Test with examples** - Validate specs with concrete cases
3. **Incremental development** - Prove small pieces, then combine
4. **Document assumptions** - Make preconditions explicit
5. **Keep proofs maintainable** - Prefer automation over manual steps
