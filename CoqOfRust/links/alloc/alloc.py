import json
import links as l

crate = "alloc"
alloc = json.load(open("alloc/alloc.json"))

print(l.get_header([
]))
print(l.pp_top_level_item(*l.find_top_level_item_by_name(crate, alloc, "Global")))
