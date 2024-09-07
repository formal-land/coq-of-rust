import json
import links as l

input_file = "core/ptr/unique.json"

with open(input_file) as f:
    input = json.load(f)

print(l.get_header([
    "links.core.marker",
    "links.core.ptr.non_null",
]))
print(l.pp_type_struct_struct(0, l.find_top_level_item_by_name(input, "Unique")))
