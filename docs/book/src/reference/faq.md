# FAQ

Frequently asked questions about rocq-of-rust.

## General

### What is rocq-of-rust?

rocq-of-rust is a tool that translates Rust programs to Rocq, enabling formal verification of Rust code using mathematical proofs.

### What is Rocq?

Rocq (formerly Coq) is an interactive proof assistant. It allows you to write mathematical definitions and theorems, and develop machine-checked proofs.

### Why formal verification?

Testing can only check a finite number of cases. Formal verification proves properties hold for *all* inputs. This is valuable for:
- Smart contracts
- Cryptographic code
- Safety-critical systems
- Protocol implementations

### How does it compare to other Rust verification tools?

| Tool | Approach | Proof Language |
|------|----------|----------------|
| **rocq-of-rust** | HIR translation | Rocq |
| **Creusot** | MIR translation | Why3 |
| **Prusti** | Viper verification | Viper |
| **Kani** | Model checking | CBMC |

rocq-of-rust provides the most expressive proof language but requires more manual effort.

## Usage

### What Rust features are supported?

Most Rust features are supported:
- Functions and methods
- Structs, enums, traits
- Generics and associated types
- Closures
- Pattern matching
- Loops and control flow

Some features have limited support:
- Async/await (partial)
- Some macro expansions
- Dynamic dispatch in complex cases

### How do I handle version mismatch errors?

Copy the `rust-toolchain` file from rocq-of-rust to your project root. This ensures you're using the same Rust nightly version.

### What if translation produces errors?

1. Check that your code compiles with `cargo check`
2. Try a simpler version of the code
3. Check for unsupported features
4. Report issues on GitHub

### How do I verify my translated code?

1. **Write links** - Resolve types using `run_symbolic`
2. **Write simulations** - Create proof-friendly models
3. **Prove equivalence** - Show simulations match links
4. **Prove properties** - Use simulations for your proofs

## Proof Writing

### How long does verification take?

This varies greatly:
- Simple functions: hours to days
- Complex algorithms: days to weeks
- Large systems: months of ongoing work

Automation (`run_symbolic`, `vm_compute`) helps significantly.

### Can proofs be automated?

Yes, partially:
- `run_symbolic` automates many linking proofs
- `vm_compute` handles concrete computations
- Standard tactics (`lia`, `auto`) solve routine goals

Complex properties still require manual proof.

### What if my proof doesn't go through?

Common issues:
1. **Wrong simulation** - Check the simulation matches Rust behavior
2. **Missing lemmas** - Search for or prove helper lemmas
3. **Timeout** - Simplify before computing
4. **Type errors** - Check implicit arguments

### How do I debug failing proofs?

1. Use `Show Proof` to see current state
2. Try smaller subgoals with `assert`
3. Check concrete cases with `vm_compute`
4. Unfold definitions one at a time

## EVM Verification

### What is the EVM project?

We're formally verifying the Ethereum Virtual Machine implementation in [revm](https://github.com/bluealloy/revm). This provides high assurance for Ethereum node software.

### What opcodes are verified?

See the [Opcode Reference](../evm/opcodes.md) for current status. Arithmetic and bitwise operations are largely complete.

### How can I contribute?

1. Pick an unverified opcode
2. Write the Link instance
3. Write a Simulation with tests
4. Submit a PR

See [Contributing](./contributing.md) for details.

## Technical

### Why HIR instead of MIR?

HIR preserves more source structure, making translated code more readable and proofs more related to the source. MIR is lower-level and harder to relate to original code.

### How are mutations handled?

We use a state monad to track mutations. Local mutations that don't escape their scope can be "forgotten" at scope exit, simplifying proofs.

### How are traits handled?

Traits become Rocq type classes. Method calls are resolved to specific implementations during linking.

### What about unsafe code?

Unsafe code is translated but the safety invariants must be manually specified and verified.

## Troubleshooting

### Build fails with "cannot find crate"

Ensure dependencies are installed:
```sh
cd RocqOfRust
opam install --deps-only .
```

### Rocq files won't compile

1. Check you're in the right opam switch
2. Run `make clean && make`
3. Ensure all dependencies are installed

### Translation produces invalid Rocq

Please report this as a bug with:
- The Rust source file
- The generated Rocq file
- The error message

### Proofs are very slow

- Use `vm_compute` instead of `simpl`
- Avoid unfolding too many definitions
- Break into smaller lemmas
- Consider if simulation can be simplified
