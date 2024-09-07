import json
import links as l

input_file = "alloc/vec/mod.json"

with open(input_file) as f:
    input = json.load(f)

print(l.get_header([
    "links.alloc.raw_vec",
]))
print(l.pp_type_struct_struct(0, l.find_top_level_item_by_name(input, "Vec")))
