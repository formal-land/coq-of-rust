import json
import os
import sys

sys.path.append(os.getcwd())

import of_json



def interpreter_interpreter_action_eof_create_inputs_types():
    crate = "revm_interpreter"
    top_level = json.load(open("revm/interpreter/interpreter_action/eof_create_inputs.json"))
    output = of_json.get_header([
        "Import revm.links.dependencies",
    ])
    output += "\n"
    (prefix, enum) = of_json.find_top_level_item_by_name(crate, top_level, "EOFCreateKind")
    output += of_json.pp_type_enum(
        prefix,
        enum["TypeEnum"],
    )
    output += "\n"

    with open("revm/interpreter/interpreter_action/links/eof_create_inputs_Types.v", "w") as f:
        f.write(output)


interpreter_interpreter_action_eof_create_inputs_types()
