import json
import links as l

crate = "move_binary_format"
input = json.load(open("move_sui/translations/move_binary_format/file_format.json"))

print(l.get_header([
    "links.alloc.alloc",
    "links.alloc.boxed",
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
    "StructHandleIndex",
    "SignatureToken",
    "Signature",
    "CompiledModule",
]


def pp_name(name: str) -> str:
    result = l.pp_top_level_item(*l.find_top_level_item_by_name(crate, input, name))

    if name == "SignatureToken":
        result = result \
            .replace(
                "move_binary_format.file_format.SignatureToken.t",
                "t"
            ) \
            .replace(
                "Inductive t : Set :=",
                "#[bypass_check(positivity=yes)] Inductive t : Set :="
            )

    return result


print("\n\n".join(pp_name(name) for name in names))
