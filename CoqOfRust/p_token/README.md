# `p-token`

A `pinocchio`-based Token program.

## Overview

`p-token` is a reimplementation of the SPL Token program, one of the most popular programs on Solana, using [`pinocchio`](https://github.com/anza-xyz/pinocchio). The purpose is to have an implementation that optimizes the compute units, while being fully compatible with the original implementation &mdash; i.e., support the exact same instruction and account layouts as SPL Token, byte for byte.

## Features

- `no_std` crate
- Same instruction and account layout as SPL Token
- Minimal CU usage


## License

The code is licensed under the [Apache License Version 2.0](LICENSE)
