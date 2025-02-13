import os


def check_link_files(parent_folder):
    # Walk through the directory tree
    for root, dirs, files in os.walk(parent_folder):
        # Check if the current directory has a 'simulations' subfolder
        if "links" in dirs:
            links_folder = os.path.join(root, "links")
            parent_files = set(
              file
              for file in files
              if file.endswith(".v")
            )
            link_files = set(
              file
              for file in os.listdir(links_folder)
              if file.endswith(".v")
            )

            extra_in_links = link_files - parent_files

            if extra_in_links:
                print(f"Files in 'links' folder of {root} but missing in parent: {extra_in_links}")


def check_simulation_files(parent_folder):
    # Walk through the directory tree
    for root, dirs, files in os.walk(parent_folder):
        # Check if the current directory has a 'simulations' subfolder
        if "simulations" in dirs:
            simulations_folder = os.path.join(root, "simulations")
            parent_files = set(
              file
              for file in files
              if file.endswith(".v")
            )
            simulation_files = set(
              file
              for file in os.listdir(simulations_folder)
              if file.endswith(".v")
            )

            missing_in_simulations = parent_files - simulation_files
            extra_in_simulations = simulation_files - parent_files

            # if missing_in_simulations:
            #     print(f"Files in {root} but missing in 'simulations': {missing_in_simulations}")

            if extra_in_simulations:
                print(f"Files in 'simulations' folder of {root} but missing in parent: {extra_in_simulations}")

            # if not missing_in_simulations and not extra_in_simulations:
            #     print(f"All files are correctly matched between {root} and its 'simulations' folder.")


check_link_files("revm")
check_simulation_files("revm")
