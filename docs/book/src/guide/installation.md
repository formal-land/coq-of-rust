# Installation

This guide covers installing rocq-of-rust and its dependencies.

## Prerequisites

- Rust toolchain (nightly)
- Rocq proof assistant (via opam)
- Python 3 (for running tests)

## Rust Installation

### Option 1: Cargo Plugin (Recommended)

Install rocq-of-rust as a cargo plugin from the repository root:

```sh
cargo install --path lib/
```

This installs the `rocq-of-rust` library and cargo plugin globally.

### Option 2: Standalone Executable

Build rocq-of-rust as a standalone binary:

```sh
cargo build --bin rocq-of-rust --release
```

The standalone executable supports translating individual files, while the cargo plugin works with entire crates.

## Rocq Installation

### Create an opam switch

```sh
opam switch create rocq-of-rust ocaml.5.1.0
```

### Activate the switch

```sh
eval $(opam env --switch=rocq-of-rust)
```

### Add Rocq repository

```sh
opam repo add rocq-released https://rocq-prover.org/opam/released
```

### Install dependencies

Navigate to the RocqOfRust directory and install:

```sh
cd RocqOfRust
opam install --deps-only .
```

### Build Rocq files

```sh
make
```

## Verification

Run the test suite to verify your installation:

```sh
python run_tests.py
```

Check for differences in generated files:

```sh
git diff
```

## Windows Setup (WSL)

For Windows users, we recommend using WSL 2:

1. **Install WSL 2** - Follow [Microsoft's official guide](https://learn.microsoft.com/en-us/windows/wsl/install)

2. **Install Rocq** - Install [Rocq](https://rocq.inria.fr/download) within WSL

3. **Install VSCode with WSL extension** - Use the [Remote - WSL extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-wsl)

4. **Configure VSCode** - In WSL terminal, run `code .` at project root, then set "Rocq: Rocq Project Root" to `.` in Remote settings

### Windows Known Issues

WSL and Windows use different file formats. For better performance:

- Place project files in WSL's `/home` directory
- Or accept slower `make` times when working from Windows filesystem

## Troubleshooting

### Version Mismatch Errors

If you encounter library version errors:

1. Copy `rust-toolchain` from rocq-of-rust root to your project
2. Ensure you're using the same nightly version

### Rocq Build Failures

Ensure all dependencies are installed:

```sh
opam install --deps-only .
```

Clean and rebuild:

```sh
make clean
make
```
