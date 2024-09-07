import json
import links as l

crate = "alloc"
raw_vec = json.load(open("alloc/raw_vec.json"))

print(l.get_header([
    "links.core.ptr.unique",
]))
print(l.pp_top_level_item(*l.find_top_level_item_by_name(crate, raw_vec, "Cap")))
print()
print(l.pp_top_level_item(*l.find_top_level_item_by_name(crate, raw_vec, "RawVecInner")))
print()
print(l.pp_top_level_item(*l.find_top_level_item_by_name(crate, raw_vec, "RawVec")))
