#!/usr/bin/env python3
"""
Generate opcode data for the EVM explorer by scanning Rocq files.

This script extracts:
1. Rust source code from comments in translated .v files
2. Link instances from links/ directories
3. Simulations from simulate/ directories
4. Test cases from tests/ directories

Output: docs/data/opcodes.json
"""

import json
import re
from pathlib import Path
from typing import Dict, List, Optional

# Path to revm instructions relative to repo root
REVM_PATH = Path("RocqOfRust/revm/revm_interpreter/instructions")

# Opcode categories and their opcodes
CATEGORIES = {
    "arithmetic": [
        "add", "mul", "sub", "div", "sdiv", "rem", "smod",
        "addmod", "mulmod", "exp", "signextend"
    ],
    "bitwise": [
        "lt", "gt", "slt", "sgt", "eq", "iszero",
        "bitand", "bitor", "bitxor", "not", "byte",
        "shl", "shr", "sar"
    ],
    "i256": [
        "i256_sign", "i256_div", "i256_rem"
    ],
    "memory": ["mload", "mstore", "mstore8", "msize", "mcopy"],
    "stack": ["pop", "push0", "push", "dup", "swap", "dupn", "swapn", "exchange"],
    "control": [
        "jump", "jumpi", "rjump", "rjumpi", "rjumpv",
        "callf", "retf", "jumpf",
        "pc", "gas", "jumpdest", "stop", "return_", "revert",
        "invalid", "nop"
    ],
    "contract": [
        "call", "call_code", "delegate_call", "static_call",
        "create", "create2", "eofcreate", "returncontract",
        "extcall", "extdelegatecall", "extstaticcall",
        "returndataload", "returndatacopy"
    ],
    "block_info": [
        "chainid", "coinbase", "timestamp", "block_number",
        "prevrandao", "gaslimit", "basefee", "blobbasefee"
    ],
    "host": [
        "balance", "selfbalance", "extcodesize", "extcodecopy", "extcodehash",
        "blockhash", "sload", "sstore", "tload", "tstore",
        "log", "selfdestruct"
    ],
    "system": [
        "keccak256", "address", "caller", "callvalue", "calldataload",
        "calldatasize", "calldatacopy", "codesize", "codecopy",
        "gasprice", "returndatasize", "origin", "blobhash"
    ],
    "data": [
        "data_load", "data_loadn", "data_size", "data_copy"
    ],
    "tx_info": [
        "gasprice", "origin", "blob_hash"
    ],
}


def find_repo_root() -> Path:
    """Find the repository root by looking for RocqOfRust directory."""
    current = Path(__file__).resolve().parent
    while current != current.parent:
        if (current / "RocqOfRust").exists():
            return current
        current = current.parent
    raise RuntimeError("Could not find repository root")


def extract_rust_source(category: str, opcode: str, repo_root: Path) -> str:
    """Extract Rust source from translated .v file comments."""
    v_file = repo_root / REVM_PATH / f"{category}.v"
    if not v_file.exists():
        return ""

    content = v_file.read_text()

    # Normalize opcode name for matching
    rust_name = opcode.rstrip("_")  # mod_ -> mod

    # Pattern to find Rust source in comments: (* pub fn name ... *)
    pattern = rf'\(\*\s*(pub fn {rust_name}\s*<[^)]+>\s*\([^)]*\)\s*\{{[^*]*\}})\s*\*\)'
    match = re.search(pattern, content, re.DOTALL | re.IGNORECASE)

    if match:
        return f"(* Original Rust from revm *)\n{match.group(1)}"

    # Try simpler pattern
    pattern2 = rf'\(\*\s*(pub fn {rust_name}[^*]+)\*\)'
    match2 = re.search(pattern2, content, re.DOTALL | re.IGNORECASE)
    if match2:
        return f"(* Original Rust from revm *)\n{match2.group(1)}"

    return ""


def extract_link(category: str, opcode: str, repo_root: Path) -> str:
    """Extract link instance definition."""
    # Check for per-opcode link file
    link_file = repo_root / REVM_PATH / "links" / category / f"{opcode}.v"
    if link_file.exists():
        return link_file.read_text()

    # Check for category-level link file
    link_file_alt = repo_root / REVM_PATH / "links" / f"{category}.v"
    if link_file_alt.exists():
        content = link_file_alt.read_text()
        # Try to extract just this opcode's instance
        pattern = rf'(Instance\s+run_{opcode}.*?(?:Defined|Qed)\.)'
        match = re.search(pattern, content, re.DOTALL)
        if match:
            return match.group(1)
        return ""

    return ""


def extract_simulation(category: str, opcode: str, repo_root: Path) -> str:
    """Extract simulation definition."""
    # Check for per-opcode simulation file
    sim_file = repo_root / REVM_PATH / "simulate" / category / f"{opcode}.v"
    if sim_file.exists():
        return sim_file.read_text()

    # Check for category-level simulation file
    sim_file_alt = repo_root / REVM_PATH / "simulate" / f"{category}.v"
    if sim_file_alt.exists():
        content = sim_file_alt.read_text()
        # Try to extract definition and lemma
        pattern = rf'(Definition\s+op_{opcode}.*?(?=Definition|Lemma|$))'
        match = re.search(pattern, content, re.DOTALL)
        if match:
            return match.group(1)

    return ""


def extract_tests(category: str, opcode: str, repo_root: Path) -> str:
    """Extract test cases for this opcode."""
    test_file = repo_root / REVM_PATH / "tests" / f"{category}.v"
    if not test_file.exists():
        return ""

    content = test_file.read_text()

    # Find all Goal statements related to this opcode
    # Pattern matches comment + Goal + Proof + Qed blocks
    pattern = rf'(\(\*\*[^*]*{opcode}[^*]*\*\)\s*Goal.*?Qed\.)'
    matches = re.findall(pattern, content, re.DOTALL | re.IGNORECASE)

    if matches:
        return "\n\n".join(matches)

    # Try finding goals with op_<opcode>
    pattern2 = rf'(Goal\s+.*?op_{opcode}.*?Qed\.)'
    matches2 = re.findall(pattern2, content, re.DOTALL)

    if matches2:
        return f"(* Test cases for {opcode.upper()} opcode *)\n\n" + "\n\n".join(matches2)

    return ""


def determine_status(rust: str, link: str, simulate: str, tests: str) -> str:
    """Determine verification status based on available code."""
    if link and simulate and tests:
        return "verified"
    elif link or simulate:
        return "in_progress"
    else:
        return "planned"


def generate_opcode_data() -> Dict:
    """Generate complete opcode data structure."""
    repo_root = find_repo_root()

    data = {
        "generated": True,
        "categories": {},
        "opcodes": {}
    }

    for category, opcodes in CATEGORIES.items():
        data["categories"][category] = {
            "name": category.replace("_", " ").title(),
            "opcodes": opcodes
        }

        for opcode in opcodes:
            rust = extract_rust_source(category, opcode, repo_root)
            link = extract_link(category, opcode, repo_root)
            simulate = extract_simulation(category, opcode, repo_root)
            tests = extract_tests(category, opcode, repo_root)

            data["opcodes"][opcode] = {
                "category": category,
                "name": opcode.upper().rstrip("_"),
                "rust": rust,
                "link": link,
                "simulate": simulate,
                "tests": tests,
                "status": determine_status(rust, link, simulate, tests)
            }

    return data


def main():
    """Generate and save opcode data."""
    print("Generating opcode data...")

    try:
        repo_root = find_repo_root()
        print(f"Repository root: {repo_root}")
    except RuntimeError as e:
        print(f"Error: {e}")
        return 1

    data = generate_opcode_data()

    # Count statistics
    verified = sum(1 for op in data["opcodes"].values() if op["status"] == "verified")
    in_progress = sum(1 for op in data["opcodes"].values() if op["status"] == "in_progress")
    planned = sum(1 for op in data["opcodes"].values() if op["status"] == "planned")
    total = len(data["opcodes"])

    print(f"Total opcodes: {total}")
    print(f"  Verified: {verified}")
    print(f"  In progress: {in_progress}")
    print(f"  Planned: {planned}")

    # Save to file
    output = repo_root / "docs" / "data" / "opcodes.json"
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(data, indent=2))

    print(f"Generated {output}")
    return 0


if __name__ == "__main__":
    exit(main())
