"""
A script to help to know which modules are in a large `.v` file.
"""
import re

with open('core.v', 'r') as file:
    lines = file.readlines()

pattern = re.compile(r'^Module (\w+)\.')

for i, line in enumerate(lines):
    match = pattern.match(line)
    if match:
        module_name = match.group(1)
        print(f'Module name: {module_name}, Line number: {i + 1}')
