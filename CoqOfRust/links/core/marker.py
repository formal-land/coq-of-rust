import json
import links as l

crate = "core"
core_marker = json.load(open("core/marker.json"))

print(l.get_header([]))
print(l.pp_top_level_item(*l.find_top_level_item_by_name(crate, core_marker, "PhantomData")))
