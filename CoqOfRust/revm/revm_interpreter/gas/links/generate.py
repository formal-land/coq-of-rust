import os
import sys

sys.path.append(os.getcwd())

import of_json


def constants():
    constants = [
        ("ZERO", 0),
        ("BASE", 2),
        ("VERYLOW", 3),
        ("DATA_LOADN_GAS", 3),
        ("CONDITION_JUMP_GAS", 4),
        ("RETF_GAS", 3),
        ("DATA_LOAD_GAS", 4),
        ("LOW", 5),
        ("MID", 8),
        ("HIGH", 10),
        ("JUMPDEST", 1),
        ("SELFDESTRUCT", 24000),
        ("CREATE", 32000),
        ("CALLVALUE", 9000),
        ("NEWACCOUNT", 25000),
        ("EXP", 10),
        ("MEMORY", 3),
        ("LOG", 375),
        ("LOGDATA", 8),
        ("LOGTOPIC", 375),
        ("KECCAK256", 30),
        ("KECCAK256WORD", 6),
        ("COPY", 3),
        ("BLOCKHASH", 20),
        ("CODEDEPOSIT", 200),
        ("ISTANBUL_SLOAD_GAS", 800),
        ("SSTORE_SET", 20000),
        ("SSTORE_RESET", 5000),
        ("REFUND_SSTORE_CLEARS", 15000),
        ("TRANSACTION_ZERO_DATA", 4),
        ("TRANSACTION_NON_ZERO_DATA_INIT", 16),
        ("TRANSACTION_NON_ZERO_DATA_FRONTIER", 68),
        ("EOF_CREATE_GAS", 32000),
        ("ACCESS_LIST_ADDRESS", 2400),
        ("ACCESS_LIST_STORAGE_KEY", 1900),
        ("COLD_SLOAD_COST", 2100),
        ("COLD_ACCOUNT_ACCESS_COST", 2600),
        ("WARM_STORAGE_READ_COST", 100),
        ("WARM_SSTORE_RESET", 5000 - 2100),  # SSTORE_RESET - COLD_SLOAD_COST
        ("INITCODE_WORD_COST", 2),
        ("CALL_STIPEND", 2300),
        ("MIN_CALLEE_GAS", 2300),
    ]
    i64_constants = [
        "SELFDESTRUCT",
        "REFUND_SSTORE_CLEARS",
    ]
    output = """(* Generated *)
Require Import CoqOfRust.CoqOfRust.
Require Import CoqOfRust.links.M.
Require Import revm_interpreter.gas.constants.
"""
    for name, value in constants:
        output += f"\nLemma {name}_eq :\n"
        output += f"  M.get_constant \"revm_interpreter::gas::constants::{name}\" =\n"
        ty = "I64" if name in i64_constants else "U64"
        output += f"  φ (Ref.immediate Pointer.Kind.Raw (Integer.Build_t IntegerKind.{ty} {value})).\n"
        output += "Proof.\n"
        output += "  repeat (autorewrite with constant_rewrites || cbn).\n"
        output += "  reflexivity.\n"
        output += "Qed.\n"
        output += f"Global Hint Rewrite {name}_eq : run_constant.\n"

    current_dir = os.path.dirname(os.path.abspath(__file__))
    output_path = os.path.join(current_dir, "constants.v")
    with open(output_path, "w") as f:
        f.write(output)


constants()
