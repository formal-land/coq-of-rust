import json
import links as l

crate = "alloc"
vec_mod = json.load(open("alloc/vec/mod.json"))

print(l.get_header([
    "links.alloc.raw_vec",
]))
print(l.pp_top_level_item(*l.find_top_level_item_by_name(crate, vec_mod, "Vec")))
