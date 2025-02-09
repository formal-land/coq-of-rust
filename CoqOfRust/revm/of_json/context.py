import json
import of_json as o

crate = "context"

def interface_host():
    input = json.load(open('../translations/context/interface/host.json'))
    output = o.get_header([])
    output += "\n"
    output += o.pp_top_level_item(*o.find_top_level_item_by_name(crate, input, "SStoreResult"))
    with open('context/interface/host.v', 'w') as f:
        f.write(output)

interface_host()
