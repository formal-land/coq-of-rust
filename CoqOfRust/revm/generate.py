import json
import os
import sys

sys.path.append(os.getcwd())

import of_json


def revm_bytecode_bytecode():
    crate = "revm_bytecode"
    top_level = json.load(open("revm/revm_bytecode/bytecode.json"))
    output = of_json.get_header([
        "Import revm.links.dependencies",
    ])
    output += "\n"
    (prefix, ty_def) = of_json.find_top_level_item_by_name(crate, top_level, "Bytecode")
    output += of_json.pp_type_enum(
        prefix,
        ty_def["TypeEnum"],
    )
    output += "\n"

    with open("revm/revm_bytecode/links/bytecode.v", "w") as f:
        f.write(output)


def revm_bytecode_eof_body():
    crate = "revm_bytecode"
    top_level = json.load(open("revm/revm_bytecode/eof/body.json"))
    output = of_json.get_header([
        "alloc.links.alloc",
        "alloc.links.vec",
        "Import revm.links.dependencies",
        "revm.revm_bytecode.eof.links.types_section",
    ])
    output += "\n"
    (prefix, ty_def) = of_json.find_top_level_item_by_name(crate, top_level, "EofBody")
    output += of_json.pp_type_struct_struct(
        prefix,
        ty_def["TypeStructStruct"],
    )
    output += "\n"

    with open("revm/revm_bytecode/eof/links/body_Types.v", "w") as f:
        f.write(output)


def revm_bytecode_eof_header():
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


def revm_bytecode_eof_types_section():
    crate = "revm_bytecode"
    top_level = json.load(open("revm/revm_bytecode/eof/types_section.json"))
    output = of_json.get_header([
        "alloc.links.alloc",
        "alloc.links.vec",
        "Import revm.links.dependencies",
    ])
    output += "\n"
    (prefix, ty_def) = of_json.find_top_level_item_by_name(crate, top_level, "TypesSection")
    output += of_json.pp_type_struct_struct(
        prefix,
        ty_def["TypeStructStruct"],
    )
    output += "\n"

    with open("revm/revm_bytecode/eof/links/types_section_Types.v", "w") as f:
        f.write(output)


def revm_bytecode_eof():
    crate = "revm_bytecode"
    top_level = json.load(open("revm/revm_bytecode/eof.json"))
    output = of_json.get_header([
        "alloc.links.alloc",
        "alloc.links.vec",
        "Import revm.links.dependencies",
        "revm.revm_bytecode.eof.links.body",
        "revm.revm_bytecode.eof.links.header",
    ])
    output += "\n"
    (prefix, ty_def) = of_json.find_top_level_item_by_name(crate, top_level, "Eof")
    output += of_json.pp_type_struct_struct(
        prefix,
        ty_def["TypeStructStruct"],
    )
    output += "\n"

    with open("revm/revm_bytecode/links/eof_Types.v", "w") as f:
        f.write(output)


def revm_interpreter_interpreter_action_eof_create_inputs():
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
    (prefix, ty_def) = of_json.find_top_level_item_by_name(crate, top_level, "EOFCreateInputs")
    output += "\n\n"
    output += of_json.pp_type_struct_struct(
        prefix,
        ty_def["TypeStructStruct"],
    )
    output += "\n"

    with open("revm/revm_interpreter/interpreter_action/links/eof_create_inputs.v", "w") as f:
        f.write(output)


# revm_bytecode_bytecode()
# revm_bytecode_eof_body()
# revm_bytecode_eof_header()
# revm_bytecode_eof_types_section()
# revm_bytecode_eof()
# revm_interpreter_interpreter_action_eof_create_inputs()

def get_all_type_definitions():
    project_path = 'revm'
    items = []
    for crate in sorted(os.listdir(project_path)):
        crate_path = os.path.join(project_path, crate)

        # Check if the crate is a directory
        if os.path.isdir(crate_path):
            print(f"Processing crate: {crate}")

            # Loop through all files in the crate directory
            for root, _, files in sorted(os.walk(crate_path)):
                for filename in sorted(files):
                    # These files are too long and make an error in JSON parsing
                    if filename == "opcode.json":
                        continue
                    # Check if the file has a .json extension
                    if filename.endswith('.json'):
                        file_path = os.path.join(root, filename)

                        # Open and read the JSON file
                        with open(file_path, 'r') as file:
                            top_level = json.load(file)
                            ty_defs = of_json.find_top_level_items_by_kind_in(
                                crate,
                                top_level,
                                ["TypeStructStruct", "TypeEnum"],
                            )
                            if len(ty_defs) > 0:
                                print(f"Found {len(ty_defs)} type definitions in {filename}")
                                for (prefix, ty_def) in ty_defs:
                                    print(f"  {prefix + [next(iter(ty_def.values()))['name']]}")
                            items += ty_defs

    # Pretty-print all the items
    output = of_json.get_header([
        "Import revm.links.dependencies",
    ])
    for (prefix, ty_def) in items:
        print(f"Type definition: {prefix + [next(iter(ty_def.values()))['name']]}")
        output += "\n"
        if "TypeEnum" in ty_def:
            output += of_json.pp_type_enum(prefix, ty_def["TypeEnum"])
        elif "TypeStructStruct" in ty_def:
            output += of_json.pp_type_struct_struct(prefix, ty_def["TypeStructStruct"])
        output += "\n"

    with open("revm/types.v", "w") as f:
        f.write(output)

get_all_type_definitions()