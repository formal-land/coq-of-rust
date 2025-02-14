import json
import os
import sys

sys.path.append(os.getcwd())

import of_json


def revm_bytecode_eof_header_types():
    crate = "revm_bytecode"
    top_level = json.load(open("revm/revm_bytecode/eof/header.json"))
    output = of_json.get_header([
        "alloc.links.alloc",
        "alloc.links.vec",
        "Import revm.links.dependencies",
    ])
    output += "\n"
    (prefix, ty_def) = of_json.find_top_level_item_by_name(crate, top_level, "EofHeader")
    output += of_json.pp_type_struct_struct(
        prefix,
        ty_def["TypeStructStruct"],
    )
    output += "\n"

    with open("revm/revm_bytecode/eof/links/header_Types.v", "w") as f:
        f.write(output)


def revm_interpreter_interpreter_action_eof_create_inputs_types():
    crate = "revm_interpreter"
    top_level = json.load(open("revm/revm_interpreter/interpreter_action/eof_create_inputs.json"))
    output = of_json.get_header([
        "Import revm.links.dependencies",
        "revm.revm_bytecode.links.eof",
    ])
    output += "\n"
    (prefix, ty_def) = of_json.find_top_level_item_by_name(crate, top_level, "EOFCreateKind")
    output += of_json.pp_type_enum(
        prefix,
        ty_def["TypeEnum"],
    )
    output += "\n"

    with open("revm/revm_interpreter/interpreter_action/links/eof_create_inputs_Types.v", "w") as f:
        f.write(output)


revm_bytecode_eof_header_types()
revm_interpreter_interpreter_action_eof_create_inputs_types()
