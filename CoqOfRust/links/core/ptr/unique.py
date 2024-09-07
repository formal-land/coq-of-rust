import json
import links as l

crate = "core"
core_ptr_unique = json.load(open("core/ptr/unique.json"))

print(l.get_header([
    "links.core.marker",
    "links.core.ptr.non_null",
]))
print(l.pp_top_level_item(*l.find_top_level_item_by_name(crate, core_ptr_unique, "Unique")))
