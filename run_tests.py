""""
Run the snapshot tests for the project by translating all the example files.

Note that we only generate the output files. We do not check them, this can be
done using the `git diff` command.
"""

import os
import subprocess
import sys


test_folder = "examples-from-rust-book"

# For each file recursively in the test folder
for root, _dirs, files in os.walk(test_folder):
    for file in files:
        base, ext = os.path.splitext(file)
        if ext == ".rs":
            # Translate the file, and save the error output if any
            command = "cargo run --quiet --bin coq-of-rust -- translate --path " +\
                os.path.join(root, file) + " 2> " +\
                os.path.join("coq_translation", root, base + ".err")
            print(command)

            try:
                subprocess.run(command, shell=True, check=True)
            except subprocess.CalledProcessError as e:
                print(f"Error occurred: {e}")
                sys.exit(1)
            except KeyboardInterrupt:
                print("Ctrl-C pressed, interrupting the script.")
                sys.exit(1)
