# Opcode Reference

This page provides a reference for all EVM opcodes being verified in rocq-of-rust.

## Reading Opcode Entries

Each opcode shows:
- **Stack effect**: [consumed] → [produced]
- **Gas cost**: Static or formula
- **Status**: ✓ Verified | ○ In Progress | - Planned

## Arithmetic Operations

### ADD (0x01)
Stack: [a, b] → [a + b]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Adds two values modulo 2^256.

### MUL (0x02)
Stack: [a, b] → [a * b]
Gas: 5 (LOW)
Status: ✓ Verified

Multiplies two values modulo 2^256.

### SUB (0x03)
Stack: [a, b] → [a - b]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Subtracts b from a, wrapping on underflow.

### DIV (0x04)
Stack: [a, b] → [a / b]
Gas: 5 (LOW)
Status: ✓ Verified

Integer division. Returns 0 if divisor is 0.

### SDIV (0x05)
Stack: [a, b] → [a /ₛ b]
Gas: 5 (LOW)
Status: ○ In Progress

Signed integer division.

### MOD (0x06)
Stack: [a, b] → [a mod b]
Gas: 5 (LOW)
Status: ○ In Progress

Modulo operation. Returns 0 if divisor is 0.

### SMOD (0x07)
Stack: [a, b] → [a modₛ b]
Gas: 5 (LOW)
Status: ○ In Progress

Signed modulo operation.

### ADDMOD (0x08)
Stack: [a, b, N] → [(a + b) mod N]
Gas: 8 (MID)
Status: ○ In Progress

Addition modulo N. Returns 0 if N is 0.

### MULMOD (0x09)
Stack: [a, b, N] → [(a * b) mod N]
Gas: 8 (MID)
Status: ○ In Progress

Multiplication modulo N. Returns 0 if N is 0.

### EXP (0x0A)
Stack: [a, b] → [a^b]
Gas: 10 + 50 * byte_size(b)
Status: ○ In Progress

Exponentiation modulo 2^256.

### SIGNEXTEND (0x0B)
Stack: [b, x] → [sign_extend(x, b)]
Gas: 5 (LOW)
Status: ○ In Progress

Sign-extends x from (b+1) bytes.

---

## Comparison & Bitwise

### LT (0x10)
Stack: [a, b] → [a < b ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Less-than comparison (unsigned).

### GT (0x11)
Stack: [a, b] → [a > b ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Greater-than comparison (unsigned).

### SLT (0x12)
Stack: [a, b] → [a <ₛ b ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Signed less-than comparison.

### SGT (0x13)
Stack: [a, b] → [a >ₛ b ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Signed greater-than comparison.

### EQ (0x14)
Stack: [a, b] → [a == b ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Equality comparison.

### ISZERO (0x15)
Stack: [a] → [a == 0 ? 1 : 0]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Check if value is zero.

### AND (0x16)
Stack: [a, b] → [a & b]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Bitwise AND.

### OR (0x17)
Stack: [a, b] → [a | b]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Bitwise OR.

### XOR (0x18)
Stack: [a, b] → [a ^ b]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Bitwise XOR.

### NOT (0x19)
Stack: [a] → [~a]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Bitwise NOT.

### BYTE (0x1A)
Stack: [i, x] → [byte_at(x, i)]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Get byte i of x (0 is most significant).

### SHL (0x1B)
Stack: [shift, value] → [value << shift]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Left shift.

### SHR (0x1C)
Stack: [shift, value] → [value >> shift]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Logical right shift.

### SAR (0x1D)
Stack: [shift, value] → [value >>ₛ shift]
Gas: 3 (VERYLOW)
Status: ✓ Verified

Arithmetic right shift (sign-extending).

---

## Memory Operations

### MLOAD (0x51)
Stack: [offset] → [value]
Gas: 3 + memory_expansion
Status: ○ In Progress

Load 32 bytes from memory.

### MSTORE (0x52)
Stack: [offset, value] → []
Gas: 3 + memory_expansion
Status: ○ In Progress

Store 32 bytes to memory.

### MSTORE8 (0x53)
Stack: [offset, value] → []
Gas: 3 + memory_expansion
Status: ○ In Progress

Store single byte to memory.

### MSIZE (0x59)
Stack: [] → [size]
Gas: 2 (BASE)
Status: ○ In Progress

Get current memory size.

### MCOPY (0x5E)
Stack: [destOffset, offset, length] → []
Gas: 3 + 3*word_count + memory_expansion
Status: ○ In Progress

Copy memory regions (EIP-5656).

---

## Stack Operations

### POP (0x50)
Stack: [a] → []
Gas: 2 (BASE)
Status: ○ In Progress

Remove top stack item.

### PUSH0 (0x5F)
Stack: [] → [0]
Gas: 2 (BASE)
Status: ○ In Progress

Push zero onto stack (EIP-3855).

### PUSH1-PUSH32 (0x60-0x7F)
Stack: [] → [value]
Gas: 3 (VERYLOW)
Status: ○ In Progress

Push 1-32 byte value onto stack.

### DUP1-DUP16 (0x80-0x8F)
Stack: [a, ...] → [a, a, ...]
Gas: 3 (VERYLOW)
Status: ○ In Progress

Duplicate Nth stack item.

### SWAP1-SWAP16 (0x90-0x9F)
Stack: [a, ..., b] → [b, ..., a]
Gas: 3 (VERYLOW)
Status: ○ In Progress

Swap top with Nth item.

### DUPN (0xE6)
Stack: [n, a, ...] → [a, n, a, ...]
Gas: 3 (VERYLOW)
Status: ○ In Progress

Duplicate Nth stack item (EOF).

### SWAPN (0xE7)
Stack: [n, a, ..., b] → [b, ..., a]
Gas: 3 (VERYLOW)
Status: ○ In Progress

Swap with Nth item (EOF).

### EXCHANGE (0xE8)
Stack: [n, m, ...] → [...]
Gas: 3 (VERYLOW)
Status: ○ In Progress

Exchange two stack items (EOF).

---

## Control Flow

### STOP (0x00)
Stack: [] → []
Gas: 0
Status: ○ In Progress

Halt execution.

### JUMP (0x56)
Stack: [dest] → []
Gas: 8 (MID)
Status: ○ In Progress

Jump to destination.

### JUMPI (0x57)
Stack: [dest, cond] → []
Gas: 10 (HIGH)
Status: ○ In Progress

Conditional jump.

### RJUMP (0xE0)
Stack: [] → []
Gas: 2 (BASE)
Status: ○ In Progress

Relative jump (EOF).

### RJUMPI (0xE1)
Stack: [cond] → []
Gas: 4
Status: ○ In Progress

Conditional relative jump (EOF).

### RJUMPV (0xE2)
Stack: [case] → []
Gas: 4
Status: ○ In Progress

Relative jump via table (EOF).

### CALLF (0xE3)
Stack: [...] → [...]
Gas: 5
Status: ○ In Progress

Call function (EOF).

### RETF (0xE4)
Stack: [...] → [...]
Gas: 3
Status: ○ In Progress

Return from function (EOF).

### JUMPF (0xE5)
Stack: [...] → [...]
Gas: 5
Status: ○ In Progress

Jump to function (EOF).

### JUMPDEST (0x5B)
Stack: [] → []
Gas: 1
Status: ○ In Progress

Mark valid jump destination.

### PC (0x58)
Stack: [] → [counter]
Gas: 2 (BASE)
Status: ○ In Progress

Get program counter.

### GAS (0x5A)
Stack: [] → [gas]
Gas: 2 (BASE)
Status: ○ In Progress

Get remaining gas.

### INVALID (0xFE)
Stack: [] → []
Gas: All remaining
Status: ○ In Progress

Invalid instruction.

---

## Contract Operations

### CALL (0xF1)
Stack: [gas, addr, value, argsOff, argsLen, retOff, retLen] → [success]
Gas: Complex formula
Status: ✓ Verified

Call another contract.

### CALLCODE (0xF2)
Stack: [gas, addr, value, argsOff, argsLen, retOff, retLen] → [success]
Gas: Complex formula
Status: ✓ Verified

Call with caller's context (deprecated).

### DELEGATECALL (0xF4)
Stack: [gas, addr, argsOff, argsLen, retOff, retLen] → [success]
Gas: Complex formula
Status: ✓ Verified

Call with caller's context and value.

### STATICCALL (0xFA)
Stack: [gas, addr, argsOff, argsLen, retOff, retLen] → [success]
Gas: Complex formula
Status: ✓ Verified

Static call (no state modification).

### CREATE (0xF0)
Stack: [value, offset, length] → [address]
Gas: 32000 + memory_expansion
Status: ○ In Progress

Create a new contract.

### CREATE2 (0xF5)
Stack: [value, offset, length, salt] → [address]
Gas: 32000 + memory_expansion + hash_cost
Status: ○ In Progress

Create with deterministic address.

### RETURN (0xF3)
Stack: [offset, length] → []
Gas: 0 + memory_expansion
Status: ○ In Progress

Return from execution.

### REVERT (0xFD)
Stack: [offset, length] → []
Gas: 0 + memory_expansion
Status: ○ In Progress

Revert state changes.

### SELFDESTRUCT (0xFF)
Stack: [address] → []
Gas: 5000 + transfer_cost
Status: ○ In Progress

Destroy contract and send funds.

---

## Block Info Operations

### BLOCKHASH (0x40)
Stack: [blockNumber] → [hash]
Gas: 20 (BLOCKHASH)
Status: ○ In Progress

Get hash of recent block.

### COINBASE (0x41)
Stack: [] → [address]
Gas: 2 (BASE)
Status: ○ In Progress

Get block's beneficiary address.

### TIMESTAMP (0x42)
Stack: [] → [timestamp]
Gas: 2 (BASE)
Status: ○ In Progress

Get block's timestamp.

### NUMBER (0x43)
Stack: [] → [blockNumber]
Gas: 2 (BASE)
Status: ○ In Progress

Get current block number.

### PREVRANDAO (0x44)
Stack: [] → [randomValue]
Gas: 2 (BASE)
Status: ○ In Progress

Get previous block's RANDAO value.

### GASLIMIT (0x45)
Stack: [] → [gasLimit]
Gas: 2 (BASE)
Status: ○ In Progress

Get block's gas limit.

### CHAINID (0x46)
Stack: [] → [chainId]
Gas: 2 (BASE)
Status: ○ In Progress

Get chain ID.

### BASEFEE (0x48)
Stack: [] → [baseFee]
Gas: 2 (BASE)
Status: ○ In Progress

Get block's base fee.

### BLOBBASEFEE (0x4A)
Stack: [] → [blobBaseFee]
Gas: 2 (BASE)
Status: ○ In Progress

Get blob base fee (EIP-4844).

---

## Host Operations

### BALANCE (0x31)
Stack: [address] → [balance]
Gas: 100-2600 (cold/warm)
Status: ○ In Progress

Get account balance.

### SELFBALANCE (0x47)
Stack: [] → [balance]
Gas: 5 (LOW)
Status: ○ In Progress

Get current contract's balance.

### EXTCODESIZE (0x3B)
Stack: [address] → [size]
Gas: 100-2600 (cold/warm)
Status: ○ In Progress

Get code size of external account.

### EXTCODECOPY (0x3C)
Stack: [address, destOffset, offset, length] → []
Gas: 100-2600 + memory_expansion
Status: ○ In Progress

Copy external code to memory.

### EXTCODEHASH (0x3F)
Stack: [address] → [hash]
Gas: 100-2600 (cold/warm)
Status: ○ In Progress

Get code hash of external account.

### SLOAD (0x54)
Stack: [key] → [value]
Gas: 100-2100 (cold/warm)
Status: ○ In Progress

Load from storage.

### SSTORE (0x55)
Stack: [key, value] → []
Gas: Complex (EIP-2200)
Status: ○ In Progress

Store to storage.

### TLOAD (0x5C)
Stack: [key] → [value]
Gas: 100
Status: ○ In Progress

Load from transient storage (EIP-1153).

### TSTORE (0x5D)
Stack: [key, value] → []
Gas: 100
Status: ○ In Progress

Store to transient storage (EIP-1153).

### LOG0-LOG4 (0xA0-0xA4)
Stack: [offset, length, topics...] → []
Gas: 375 + 8*length + 375*topic_count
Status: ○ In Progress

Emit log event.

---

## System Operations

### KECCAK256 (0x20)
Stack: [offset, length] → [hash]
Gas: 30 + 6*word_count + memory_expansion
Status: ○ In Progress

Compute Keccak-256 hash.

### ADDRESS (0x30)
Stack: [] → [address]
Gas: 2 (BASE)
Status: ○ In Progress

Get current contract address.

### CALLER (0x33)
Stack: [] → [address]
Gas: 2 (BASE)
Status: ○ In Progress

Get caller address.

### CALLVALUE (0x34)
Stack: [] → [value]
Gas: 2 (BASE)
Status: ○ In Progress

Get deposited value.

### CALLDATALOAD (0x35)
Stack: [offset] → [data]
Gas: 3 (VERYLOW)
Status: ○ In Progress

Load 32 bytes from call data.

### CALLDATASIZE (0x36)
Stack: [] → [size]
Gas: 2 (BASE)
Status: ○ In Progress

Get call data size.

### CALLDATACOPY (0x37)
Stack: [destOffset, offset, length] → []
Gas: 3 + 3*word_count + memory_expansion
Status: ○ In Progress

Copy call data to memory.

### CODESIZE (0x38)
Stack: [] → [size]
Gas: 2 (BASE)
Status: ○ In Progress

Get code size.

### CODECOPY (0x39)
Stack: [destOffset, offset, length] → []
Gas: 3 + 3*word_count + memory_expansion
Status: ○ In Progress

Copy code to memory.

### RETURNDATASIZE (0x3D)
Stack: [] → [size]
Gas: 2 (BASE)
Status: ○ In Progress

Get return data size.

### RETURNDATACOPY (0x3E)
Stack: [destOffset, offset, length] → []
Gas: 3 + 3*word_count + memory_expansion
Status: ○ In Progress

Copy return data to memory.

---

## Transaction Info

### GASPRICE (0x3A)
Stack: [] → [gasPrice]
Gas: 2 (BASE)
Status: ○ In Progress

Get gas price.

### ORIGIN (0x32)
Stack: [] → [address]
Gas: 2 (BASE)
Status: ○ In Progress

Get transaction origin.

### BLOBHASH (0x49)
Stack: [index] → [hash]
Gas: 3 (VERYLOW)
Status: ○ In Progress

Get blob versioned hash (EIP-4844).

---

## Data Operations (EOF)

### DATALOAD (0xD0)
Stack: [offset] → [data]
Gas: 4
Status: ○ In Progress

Load data from data section.

### DATALOADN (0xD1)
Stack: [] → [data]
Gas: 3
Status: ○ In Progress

Load data with immediate offset.

### DATASIZE (0xD2)
Stack: [] → [size]
Gas: 2
Status: ○ In Progress

Get data section size.

### DATACOPY (0xD3)
Stack: [destOffset, offset, length] → []
Gas: 3 + 3*word_count + memory_expansion
Status: ○ In Progress

Copy data section to memory.

---

## Gas Constants

| Name | Value | Used By |
|------|-------|---------|
| ZERO | 0 | STOP |
| BASE | 2 | POP, PC, MSIZE |
| VERYLOW | 3 | ADD, SUB, LT, GT, etc. |
| LOW | 5 | MUL, DIV, MOD |
| MID | 8 | ADDMOD, MULMOD, JUMP |
| HIGH | 10 | JUMPI |

## Source Files

Verification code is located at:
```
RocqOfRust/revm/revm_interpreter/instructions/
├── arithmetic.v         # Translated Rust
├── bitwise.v
├── links/
│   ├── arithmetic.v     # Type linking
│   └── bitwise/         # Per-opcode links
├── simulate/
│   ├── arithmetic.v     # Simulation models
│   └── bitwise/
└── tests/
    ├── arithmetic.v     # Test cases
    └── bitwise.v
```
