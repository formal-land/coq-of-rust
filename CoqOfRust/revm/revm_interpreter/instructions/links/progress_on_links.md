# Progress on links

> This file is generated automatically by `count_admitted.py`

## Arithmetic

- ✅ `add`
- ✅ `mul`
- ✅ `sub`
- ✅ `div`
- ✅ `sdiv`
- ✅ `rem`
- ✅ `smod`
- ✅ `addmod`
- ✅ `mulmod`
- ❌ `exp`
- ❌ `signextend`

## Block_info

- ✅ `chainid`
- ❌ `coinbase`
- ✅ `timestamp`
- ✅ `block_number`
- ❌ `difficulty`
- ✅ `gaslimit`
- ✅ `basefee`
- ✅ `blob_basefee`

## Contract

- ❌ `eofcreate`
- ❌ `return_contract`
- ❌ `extcall_input`
- ❌ `extcall_gas_calc`
- ❌ `pop_extcall_target_address`
- ❌ `extcall`
- ❌ `extdelegatecall`
- ❌ `extstaticcall`
- ❌ `create`
- ❌ `call`
- ❌ `call_code`
- ❌ `delegate_call`
- ❌ `static_call`

## Control

- ❌ `rjump`
- ❌ `rjumpi`
- ❌ `rjumpv`
- ❌ `jump`
- ❌ `jumpi`
- ❌ `jump_inner`
- ❌ `jumpdest_or_nop`
- ❌ `callf`
- ❌ `retf`
- ❌ `jumpf`
- ❌ `pc`
- ❌ `return_inner`
- ❌ `ret`
- ❌ `revert`
- ✅ `stop`
- ❌ `invalid`
- ✅ `unknown`

## Data

- ❌ `data_load`
- ❌ `data_loadn`
- ❌ `data_size`
- ❌ `data_copy`

## Host

- ❌ `balance`
- ❌ `selfbalance`
- ❌ `extcodesize`
- ❌ `extcodehash`
- ❌ `extcodecopy`
- ❌ `blockhash`
- ❌ `sload`
- ❌ `sstore`
- ❌ `tstore`
- ❌ `tload`
- ❌ `log`
- ❌ `selfdestruct`

## I256

- ❌ `i256_sign`
- ❌ `i256_sign_compl`
- ❌ `u256_remove_sign`
- ❌ `two_compl_mut`
- ❌ `i256_cmp`
- ❌ `i256_div`
- ❌ `i256_mod`

## Memory

- ❌ `mload`
- ❌ `mstore`
- ❌ `mstore8`
- ❌ `msize`
- ❌ `mcopy`

## Stack

- ✅ `pop`
- ❌ `push0`
- ❌ `push`
- ❌ `dup`
- ❌ `swap`
- ✅ `dupn`
- ✅ `swapn`
- ❌ `exchange`

## System

- ❌ `keccak256`
- ❌ `address`
- ❌ `caller`
- ❌ `codesize`
- ❌ `codecopy`
- ❌ `calldataload`
- ✅ `calldatasize`
- ✅ `callvalue`
- ❌ `memory_resize`
- ❌ `calldatacopy`
- ❌ `returndatasize`
- ❌ `returndatacopy`
- ❌ `returndataload`
- ❌ `gas`

## Tx_info

- ❌ `gasprice`
- ❌ `origin`
- ❌ `blob_hash`

## Utility

- ❌ `cast_slice_to_u256`

## Summary

- Total: 103
- Admitted: 81
- Defined: 22
- Percentage: 21.36%
