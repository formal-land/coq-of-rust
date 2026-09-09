# EVM Verification

rocq-of-rust is being used to formally verify the Ethereum Virtual Machine (EVM) implementation in the [revm](https://github.com/bluealloy/revm) project.

## What is the EVM?

The Ethereum Virtual Machine is a stack-based virtual machine that executes smart contracts on the Ethereum blockchain. It processes opcodes that manipulate:

- A 256-bit wide **stack** (max 1024 items)
- **Memory** (byte-addressed, expandable)
- **Storage** (persistent key-value store)
- **Call data** and **return data**

## Why Verify the EVM?

The EVM handles billions of dollars in assets. Bugs in EVM implementations can lead to:

- Consensus failures between nodes
- Exploitable vulnerabilities
- Loss of funds

Formal verification provides mathematical certainty that the implementation matches the specification.

## Verification Approach

We verify each opcode through four stages:

```
┌─────────────┐     ┌─────────────┐     ┌─────────────┐     ┌─────────────┐
│   1. Rust   │ ──► │  2. Link    │ ──► │ 3.Simulate  │ ──► │  4. Test    │
│   Source    │     │   Types     │     │   Model     │     │   Cases     │
└─────────────┘     └─────────────┘     └─────────────┘     └─────────────┘
```

1. **Rust Source** - Original revm implementation (translated to Rocq)
2. **Link** - Type-resolved version with trait instances
3. **Simulate** - Idiomatic Rocq model for proofs
4. **Test** - Concrete test cases validating behavior

## Opcode Categories

| Category | Examples | Description |
|----------|----------|-------------|
| **Arithmetic** | ADD, MUL, SUB, DIV | Basic math operations |
| **Comparison** | LT, GT, EQ, ISZERO | Compare stack values |
| **Bitwise** | AND, OR, XOR, NOT | Bit manipulation |
| **Stack** | PUSH, POP, DUP, SWAP | Stack operations |
| **Memory** | MLOAD, MSTORE, MSIZE | Memory access |
| **Control** | JUMP, JUMPI, STOP | Control flow |
| **Contract** | CALL, CREATE, RETURN | Contract interaction |

## Progress

Current verification progress on EVM opcodes:

**Summary: 121 link instances | 25 simulation files | 3 test files**

### Fully Verified (Link + Simulate + Tests)

The following 22 opcodes have complete verification coverage:

**Bitwise & Comparison (14 opcodes):**
- `LT`, `GT`, `EQ`, `ISZERO`
- `SLT`, `SGT` (signed comparison)
- `AND`, `OR`, `XOR`, `NOT`
- `BYTE`
- `SHL`, `SHR`, `SAR` (shifts)

**Arithmetic (4 opcodes):**
- `ADD`, `SUB`, `MUL`, `DIV`

**Contract (4 opcodes):**
- `CALL`, `CALLCODE`, `DELEGATECALL`, `STATICCALL`

### In Progress (Link Only)

The following categories have link instances but are awaiting simulation/tests:

**Arithmetic (7 more):**
- `SDIV`, `MOD`, `SMOD`, `ADDMOD`, `MULMOD`, `EXP`, `SIGNEXTEND`

**Contract (9 more):**
- `CREATE`, `CREATE2`, `EOFCREATE`, `RETURNCONTRACT`
- `EXTCALL`, `EXTDELEGATECALL`, `EXTSTATICCALL`
- `RETURNDATALOAD`, `RETURNDATACOPY`

**Memory (5 opcodes):**
- `MLOAD`, `MSTORE`, `MSTORE8`, `MSIZE`, `MCOPY`

**Stack (8 opcodes):**
- `POP`, `PUSH0`, `PUSH`
- `DUP`, `SWAP`, `DUPN`, `SWAPN`, `EXCHANGE`

**Control (17 opcodes):**
- `JUMP`, `JUMPI`, `RJUMP`, `RJUMPI`, `RJUMPV`
- `CALLF`, `RETF`, `JUMPF`
- `RETURN`, `REVERT`, `STOP`, `INVALID`
- `PC`, `GAS`, `JUMPDEST`, `NOP`

**Block Info (8 opcodes):**
- `CHAINID`, `COINBASE`, `TIMESTAMP`, `BLOCKNUMBER`
- `PREVRANDAO`, `GASLIMIT`, `BASEFEE`, `BLOBBASEFEE`

**Host (12 opcodes):**
- `BALANCE`, `SELFBALANCE`, `EXTCODESIZE`, `EXTCODECOPY`, `EXTCODEHASH`
- `BLOCKHASH`, `SLOAD`, `SSTORE`, `TLOAD`, `TSTORE`
- `LOG`, `SELFDESTRUCT`

**System (14 opcodes):**
- `KECCAK256`, `ADDRESS`, `CALLER`, `CALLVALUE`, `CALLDATALOAD`
- `CALLDATASIZE`, `CALLDATACOPY`, `CODESIZE`, `CODECOPY`
- `GASPRICE`, `RETURNDATASIZE`, `ORIGIN`
- `BLOBHASH`, `MCOPY`

**Data (4 opcodes):**
- `DATALOAD`, `DATALOADN`, `DATASIZE`, `DATACOPY`

**TX Info (3 opcodes):**
- `GASPRICE`, `ORIGIN`, `BLOBHASH`

### Planned

- Precompiles
- Additional EOF opcodes

## Explore the Code

- [**Interactive Explorer**](./explorer.md) - Browse opcodes with syntax highlighting
- [**Opcode Reference**](./opcodes.md) - Complete opcode documentation
- [Source on GitHub](https://github.com/formal-land/rocq-of-rust/tree/main/RocqOfRust/revm/revm_interpreter/instructions)

## Technical Details

### Interpreter State

The EVM interpreter state includes:

```rocq
Record Interpreter.t := {
  stack : Stack.t;          (* 256-bit values *)
  memory : Memory.t;        (* byte array *)
  gas : Gas.t;              (* remaining gas *)
  control : Control.t;      (* instruction result *)
  (* ... other fields *)
}.
```

### Gas Accounting

Every opcode consumes gas. We verify gas is correctly deducted:

```rocq
Definition gas_macro interpreter cost ... :=
  if interpreter.(gas) <? cost then
    (* Out of gas error *)
  else
    (* Deduct and continue *)
```

### Stack Discipline

Stack operations are verified to:
- Check for underflow (popping empty stack)
- Check for overflow (pushing past 1024)
- Correctly manipulate values

## Contributing

We welcome contributions to EVM verification:

1. Pick an unverified opcode
2. Write the Link instance (often automated by `run_symbolic`)
3. Write the Simulation with test cases
4. Submit a PR

See [Contributing](../reference/contributing.md) for detailed guidelines.
