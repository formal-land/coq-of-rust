import json
import links as l

crate = "core"
core_ptr_non_null = json.load(open("core/ptr/non_null.json"))

print(l.get_header([]))
print(l.pp_top_level_item(*l.find_top_level_item_by_name(crate, core_ptr_non_null, "NonNull")))
