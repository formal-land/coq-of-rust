# Contributing

We welcome contributions to rocq-of-rust! Here's how to get involved.

## Ways to Contribute

### 1. EVM Opcode Verification

The most impactful contribution is verifying EVM opcodes:

1. Check the [opcode reference](../evm/opcodes.md) for unverified opcodes
2. Write a Link instance
3. Write a Simulation with tests
4. Submit a PR

### 2. Documentation

Improve docs by:
- Fixing typos and errors
- Adding examples
- Clarifying confusing sections
- Translating to other languages

### 3. Bug Reports

Report issues with:
- Clear reproduction steps
- Rust source that fails
- Generated Rocq (if available)
- Error messages

### 4. Tool Improvements

Improve the translator:
- Better error messages
- New Rust feature support
- Performance improvements
- Better output formatting

## Development Setup

### 1. Clone the Repository

```sh
git clone https://github.com/formal-land/rocq-of-rust.git
cd rocq-of-rust
```

### 2. Set Up Rust

```sh
# Uses rust-toolchain file automatically
cargo build
```

### 3. Set Up Rocq

```sh
opam switch create rocq-of-rust ocaml.5.1.0
eval $(opam env --switch=rocq-of-rust)
opam repo add rocq-released https://rocq-prover.org/opam/released
cd RocqOfRust
opam install --deps-only .
make
```

### 4. Run Tests

```sh
python run_tests.py
```

## EVM Contribution Workflow

### Step 1: Choose an Opcode

Look at `RocqOfRust/revm/revm_interpreter/instructions/` to find opcodes without Link/Simulation files.

### Step 2: Write the Link

Create a file in the appropriate `links/` directory:

```rocq
(* RocqOfRust/revm/revm_interpreter/instructions/links/bitwise/my_op.v *)
Require Import RocqOfRust.RocqOfRust.
Require Import links.RocqOfRust.
(* ... other imports ... *)

Instance run_my_op
    {WIRE H : Set} `{Link WIRE} `{Link H}
    {WIRE_types : InterpreterTypes.Types.t}
    `{InterpreterTypes.Types.AreLinks WIRE_types}
    (run_InterpreterTypes_for_WIRE : InterpreterTypes.Run WIRE WIRE_types)
    (interpreter : '&mut (Interpreter.t WIRE WIRE_types))
    (_host : '&mut H) :
  Run.Trait
    instructions.bitwise.my_op [] [ Φ WIRE; Φ H ] [ φ interpreter; φ _host ]
    unit.
Proof.
  constructor.
  run_symbolic.
Defined.
Global Opaque run_my_op.
```

### Step 3: Write the Simulation

Create a file in the appropriate `simulate/` directory:

```rocq
(* RocqOfRust/revm/revm_interpreter/instructions/simulate/bitwise/my_op.v *)
Require Import simulate.RocqOfRust.
(* ... imports ... *)

Definition op_my_op
    {WIRE : Set} `{Link WIRE}
    {WIRE_types : InterpreterTypes.Types.t}
    `{InterpreterTypes.Types.AreLinks WIRE_types}
    `{!InterpreterTypes.C WIRE_types}
    (interpreter : Interpreter.t WIRE WIRE_types) :
    Interpreter.t WIRE WIRE_types :=
  (* Implementation using macros *)
  gas_macro interpreter constants.VERYLOW id (fun interpreter =>
    (* Stack manipulation and computation *)
  ).

Lemma op_my_op_eq
    (* ... type parameters ... *)
    (interpreter : Interpreter.t WIRE WIRE_types)
    (_host : H) :
  (* Equivalence statement *)
Proof.
  (* Proof that simulation equals linked code *)
Qed.
```

### Step 4: Add Tests

Add test cases to the appropriate test file:

```rocq
(* In tests/bitwise.v or similar *)

(** Test description *)
Goal
  let stack := {| Stack.value := [
    {| Uint.value := test_input_1 |};
    {| Uint.value := test_input_2 |}
  ] |} in
  let interpreter := make_interpreter stack in
  let result := op_my_op interpreter in
  result.(Interpreter.stack).(Stack.value) = [{| Uint.value := expected |}].
Proof.
  timeout 1 vm_compute.
  reflexivity.
Qed.
```

### Step 5: Update Build

Add new files to `_CoqProject` if needed.

### Step 6: Submit PR

1. Create a branch: `git checkout -b verify-my-op`
2. Commit changes: `git commit -am "Verify MY_OP opcode"`
3. Push and create PR

## Code Style

### Rocq

- Use 2-space indentation
- Align similar constructs vertically
- Add documentation comments for definitions
- Use meaningful names

### Rust

- Follow standard Rust style (`cargo fmt`)
- Add comments for complex logic
- Include doctests where appropriate

## Review Process

1. **CI checks** - All tests must pass
2. **Code review** - Maintainer reviews changes
3. **Proof review** - Proofs are checked for correctness
4. **Documentation** - Changes should include docs updates

## Getting Help

- Open an issue for questions
- Join discussions on GitHub
- Check existing issues for similar problems

## License

Contributions are licensed under the same terms as the project (see LICENSE file).
