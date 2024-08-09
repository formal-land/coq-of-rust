# Installation and Build Tutorial

This tutorial provides an introduction to how to build `coq-of-rust`.
The first part of the tutorial describes two possible ways to build
the Rust to Coq translator (implemented in Rust): as a cargo plugin or
as a standalone executable. The second part of the tutorial describes
how to install dependencies and build the Coq implementation of Rust
shallow embedding and facilities to verify Rust programs. After you
successfully built `coq-of-rust` you can take a look at our [user
guide](./GUIDE.md)

## Table of Contents

- [Rust](#rust)
  - [Cargo plugin](#cargo-plugin)
  - [Standalone executable](#standalone-executable)
  - [Tests](#tests)
- [Coq](#coq)
- [For Windows](#for-windows)

## Rust

### Cargo plugin

In order to install `coq-of-rust` run the following command from the
root of this repository:
```sh
cargo install --path lib/
```

This command would build and install the `coq-of-rust` library and
the cargo plugin.

Then, in any Rust project, generate a `Crate.v` file with the Coq
translation of the crate using this command:
```sh
cargo coq-of-rust
```

See the `coq-of-rust` [user guide](./GUIDE.md) for more details about
using `coq-of-rust`.

### Standalone executable

Additionally, it is also possible to build `coq-of-rust` as a
standalone executable. This method has an advantage of supporting the
translation of individual files, while the cargo plugin only supports
the translation of the whole crates.

The following command would build `coq-of-rust` as a standalone
executable (in release mode):
```sh
cargo build --bin coq-of-rust --release
```

Using `coq-of-rust` as a standalone executable is intended for testing
purposes. We generally recommend to use the cargo plugin instead.

### Tests

The following command allows to regenerate the snapshots of the
translations of the test files:
```sh
python run_tests.py
```

If `coq-of-rust` would fail to translate some of the test files, it
would produce a file with an error instead.

Check if some freshly generated translation results differ to those
included in the repository:
```sh
git diff
```

## Coq

In order to install dependencies and build the Coq part of the project
run the following commands.

Create a new opam switch:
```sh
opam switch create coq-of-rust ocaml.5.1.0
```

Update shell environment to use the new switch:
```sh
eval $(opam env --switch=coq-of-rust)
```

Add the repository with Coq packages:
```sh
opam repo add coq-released https://coq.inria.fr/opam/released
```

Go to the directory with Coq files:
```sh
cd CoqOfRust
```

Install the required dependencies:
```sh
opam install --deps-only .
```

Compile the Coq files:
```sh
make
```


## For Windows

On Windows, to set up the environment to `make` the Rust files you 
need to translate, follow the belows:

1. Install WSL2 by [the official tutorial](https://learn.microsoft.com/en-us/windows/wsl/install) with a proper Linux distribution
2. Install [Coq](https://coq.inria.fr/download) in WSL 2
3. Install [VSCode](https://code.visualstudio.com/), its [WSL](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-wsl) 
extension and its [Coq](https://marketplace.visualstudio.com/items?itemName=ruoz.coq) 
extension
4. Follow the [official guide](https://code.visualstudio.com/docs/remote/wsl) 
to run the Coq project in WSL environment. Specifically:
   1. With an WSL terminal, enter `code .` at the project root that 
   you want to run `CoqOfRust`
   2. With `Ctrl+,` for VSCode's settings, checkout the environment 
   settings for `Remote: [WSL ...]`. Modify the `Coq: Coq Project Root` 
   to `.` , in particular, your preference folder with `_CoqProject` 
   inside
   3. Now you can `make` your project in WSL(not Windows) or customize 
   your experience with other features of `CoqOfRust`

### Known Issues: 

WSL has a different format from `Windows`. Since we run Coq on `WSL` 
only, the files being generated should be in WSL's file format. We 
usually put the project on Windows, `make` it in WSL, to generate 
Coq files of `WSL`'s file format. The format differences here usually
lead to significantly longer `make` time for WSL than other systems. 

As an alternative, you might copy the project under WSL's `/mnt` and
observe the performance boost under WSL's `make`, with a tradeoff of
extra time on copying the project from Windows to WSL.