# Count the number of admitted instances in the current folder
import os

print("# Progress on links")
print()
print("> This file is generated automatically by `count_admitted.py`")

total = 0
admitted = 0
defined = 0

for file in sorted(os.listdir(".")):
    if file.endswith(".v"):
        # Mardown title
        print()
        print(f"## {file.replace('.v', '').capitalize()}")
        print()
        with open(file, "r") as f:
            for index, line in enumerate(f):
                # print(line)
                if "Instance run_" in line:
                    total += 1
                    # Get the name of the instance
                    instance_name = line.split("Instance run_")[1].split("]")[0].strip()
                    # Get the first word of the instance name
                    instance_name = instance_name.split(" ")[0]
                    # To know if it is admitted, we need to know which word appears first
                    # in the lines after:
                    # "Admitted" or "Defined"
                    isAdmitted = False
                    with open(file, "r") as f:
                        for following_line in list(f)[index + 1 :]:
                            if "Admitted" in following_line:
                                isAdmitted = True
                                break
                            if "Defined" in following_line:
                                break
                    emoji = "[ ]" if isAdmitted else "[x]"
                    if isAdmitted:
                        admitted += 1
                    else:
                        defined += 1
                    print(f"- {emoji} `{instance_name}`")

print()
print("## Summary")
print()
print(f"- Total: {total}")
print(f"- Admitted: {admitted}")
print(f"- Defined: {defined}")
# With 2 decimal places, of defined
print(f"- Percentage: {defined / total * 100:.2f}%")
