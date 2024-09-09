import json
import links as l

crate = "alloc"
boxed = json.load(open("alloc/boxed.json"))

print(l.get_header([
    "links.core.ptr.unique",
]))
print(l.pp_top_level_item(*l.find_top_level_item_by_name(crate, boxed, "Box")))
