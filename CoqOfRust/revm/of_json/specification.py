import json
import of_json as o

crate = "specification"

def hardfork():
    input = json.load(open('../translations/specification/hardfork.json'))
    output = o.get_header([])
    output += "\n"
    output += o.pp_top_level_item(*o.find_top_level_item_by_name(crate, input, "SpecId"))
    with open('specification/hardfork.v', 'w') as f:
        f.write(output)

hardfork()
