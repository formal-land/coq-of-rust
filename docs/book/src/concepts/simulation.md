# Simulation: Functional Models

Simulations are hand-written Rocq definitions that model Rust code in a proof-friendly way. They're designed for verification, not execution fidelity.

## Purpose

While linking produces executable Rocq code that mirrors Rust, simulations provide:

1. **Simplicity** - Remove unnecessary complexity for proofs
2. **Abstraction** - Use mathematical types (`Z`) instead of machine types
3. **Composability** - Structure for compositional reasoning
4. **Efficiency** - Fast proof checking via `vm_compute`

## Simulation vs Linked Code

| Aspect | Linked Code | Simulation |
|--------|-------------|------------|
| Purpose | Faithful execution | Easy proofs |
| Integers | Tagged machine types | Unbounded `Z` |
| References | Explicit pointers | Direct values |
| Complexity | Matches Rust | Simplified |

## Example: EVM LT Opcode

### Linked Version

```rocq
Instance run_lt ... :
  Run.Trait instructions.bitwise.lt [] [Φ WIRE; Φ H] [φ interpreter; φ _host]
    unit.
Proof.
  constructor.
  run_symbolic.
Defined.
```

### Simulation Version

```rocq
Definition op_lt
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t}
    `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
  popn_top_macro interpreter {| Integer.value := 1 |} id (fun arr top interpreter =>
    let '{| ArrayPair.x := op1 |} := arr.(array.value) in
    let op2 := top.(RefStub.projection) interpreter.(Interpreter.stack) in
    let result :=
      if PartialOrd.lt op1 op2 then
        {| Uint.value := 1 |}
      else
        {| Uint.value := 0 |} in
    let stack :=
      top.(RefStub.injection)
        interpreter.(Interpreter.stack) result in
    interpreter <| Interpreter.stack := stack |>
  )).
```

Key differences:
- Returns the new interpreter state directly
- Uses helper macros (`gas_macro`, `popn_top_macro`)
- Operates on structured data instead of raw values
- No monadic plumbing

## Design Principles

### 1. Use Mathematical Types

Replace machine integers with `Z`:

```rocq
(* Instead of *)
Definition add_u64 (a b : u64) : u64 := ...

(* Use *)
Definition add (a b : Z) : Z := a + b.
```

### 2. Remove Unnecessary Indirection

If a reference is only used to avoid copying:

```rocq
(* Rust uses &T for efficiency *)
fn process(data: &Vec<u8>) -> usize { data.len() }

(* Simulation uses direct value *)
Definition process (data : list Z) : Z := Z.of_nat (length data).
```

### 3. Index with Z, not Pointers

```rocq
(* Instead of pointer arithmetic *)
Definition get_at_ptr (base : Pointer) (offset : nat) : M Value := ...

(* Use list indexing *)
Definition get_at (arr : list Z) (idx : Z) : option Z :=
  nth_error arr (Z.to_nat idx).
```

### 4. Structured State Updates

Use record update notation:

```rocq
interpreter <| Interpreter.stack := new_stack |>
           <| Interpreter.gas := new_gas |>
```

## Proving Equivalence

After writing a simulation, prove it equals the linked code:

```rocq
Lemma op_lt_eq
    {WIRE H : Set} `{Link WIRE} `{Link H}
    (* ... type parameters ... *)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  let ref_interpreter : '&mut (Interpreter.t WIRE WIRE_types) := make_ref 0 in
  let ref_host : '&mut H := make_ref 1 in
  {{
    SimulateM.eval_f
      (run_lt run_InterpreterTypes_for_WIRE ref_interpreter ref_host)
      ([interpreter; _host]%stack) 🌲
    (
      Output.Success tt,
      [op_lt interpreter; _host]%stack
    )
  }}.
Proof.
  intros.
  unfold op_lt.
  gas_macro_eq InterpreterTypesEq.
  popn_top_macro_eq InterpreterTypesEq.
  (* ... proof steps ... *)
Qed.
```

The proof shows that running the linked `run_lt` produces the same result as `op_lt`.

## Testing Simulations

Use `Goal` statements with `vm_compute`:

```rocq
(** Test that LT correctly computes 25 < 23 = false *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := 25 |};
    {| Uint.value := 23 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_lt interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := 0 |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
```

Benefits:
- Validates simulation correctness
- Catches mistakes early
- Fast execution via `vm_compute`
- Serves as documentation

## Common Patterns

### State Monad Macros

```rocq
Definition gas_macro interpreter cost on_fail on_success :=
  if interpreter.(Interpreter.gas) <? cost then
    on_fail interpreter
  else
    on_success (interpreter <| Interpreter.gas :=
      interpreter.(Interpreter.gas) - cost |>).
```

### Stack Manipulation

```rocq
Definition pop_stack (s : Stack.t) : option (Uint.t * Stack.t) :=
  match s.(Stack.value) with
  | [] => None
  | h :: t => Some (h, {| Stack.value := t |})
  end.
```

### Error Handling

```rocq
Definition with_result {A B} (m : option A) (f : A -> B) (err : B) : B :=
  match m with
  | Some a => f a
  | None => err
  end.
```

## Next Steps

Once simulations are written and proven equivalent to linked code, you can write [proofs](./proofs.md) about program properties using the simulations.
