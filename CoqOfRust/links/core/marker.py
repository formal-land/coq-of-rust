import json
import links as l

input_file = "core/marker.json"

with open(input_file) as f:
    input = json.load(f)

print(l.get_header([]))
print(l.pp_type_struct_tuple(0, l.find_top_level_item_by_name(input, "PhantomData")))
