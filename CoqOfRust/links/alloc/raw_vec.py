import json
import links as l

input_file = "alloc/raw_vec.json"

with open(input_file) as f:
    input = json.load(f)

print(l.get_header([
    "links.core.ptr.unique",
]))
print(l.pp_type_struct_tuple(0, l.find_top_level_item_by_name(input, "Cap")))
print()
print(l.pp_type_struct_struct(0, l.find_top_level_item_by_name(input, "RawVecInner")))
print()
print(l.pp_type_struct_struct(0, l.find_top_level_item_by_name(input, "RawVec")))
