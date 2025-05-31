# Count the number of admitted instances in the current folder
import os

print("# Progress on links")
print()
print("> This file is generated automatically by `count_admitted.py`")

total = 0
admitted = 0
defined = 0


def count_in_folder(folder: str):
    for file in sorted(os.listdir(folder)):
        if file.endswith(".v"):
            # Mardown title
            print()
            folder_in_title = "" if folder == "." else folder.capitalize() + "/"
            print(f"## {folder_in_title}{file.replace('.v', '').capitalize()}")
            print()
            with open(os.path.join(folder, file), "r") as f:
                for index, line in enumerate(f):
                    # print(line)
                    if "Instance run_" in line:
                        global total
                        total += 1
                        # Get the name of the instance
                        instance_name = line.split("Instance run_")[1].split("]")[0].strip()
                        # Get the first word of the instance name
                        instance_name = instance_name.split(" ")[0]
                        # To know if it is admitted, we need to know which word appears first
                        # in the lines after:
                        # "Admitted" or "Defined"
                        isAdmitted = False
                        with open(os.path.join(folder, file), "r") as f:
                            for following_line in list(f)[index + 1 :]:
                                if "Admitted" in following_line:
                                    isAdmitted = True
                                    break
                                if "Defined" in following_line:
                                    break
                        emoji = "[ ]" if isAdmitted else "[x]"
                        if isAdmitted:
                            global admitted
                            admitted += 1
                        else:
                            global defined
                            defined += 1
                        print(f"- {emoji} `{instance_name}`")

count_in_folder(".")
count_in_folder("contract")

print()
print("## Summary")
print()
print(f"- Total: {total}")
print(f"- Admitted: {admitted}")
print(f"- Defined: {defined}")
# With 2 decimal places, of defined
print(f"- Percentage: {defined / total * 100:.2f}%")
