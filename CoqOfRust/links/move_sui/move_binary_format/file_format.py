import json
import links as l

crate = "move_binary_format"
input = json.load(open("move_sui/translations/move_binary_format/file_format.json"))

print(l.get_header([
    "links.alloc.alloc",
    "links.alloc.vec",
]))
names = [
    "AbilitySet",
    "StructTypeParameter",
    "ModuleHandleIndex",
    "AddressIdentifierIndex",
    "IdentifierIndex",
    "ModuleHandle",
    "StructHandle",
    "SignatureIndex",
    "FunctionHandle",
    "StructDefinitionIndex",
    "FieldHandle",
    "StructDefInstantiation",
    "FunctionHandleIndex",
    "FunctionInstantiation",
    "FieldHandleIndex",
    "FieldInstantiation",
    "SignatureToken",
    "Signature",
    "CompiledModule",
]
print("\n\n".join(
    l.pp_top_level_item(*l.find_top_level_item_by_name(crate, input, name))
    for name in names
))
