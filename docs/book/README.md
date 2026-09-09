# rocq-of-rust Documentation

This directory contains the mdbook-based documentation for rocq-of-rust.

## Prerequisites

- [mdbook](https://rust-lang.github.io/mdBook/) - Install with `cargo install mdbook` or download from releases
- Python 3 (for opcode data generation)

## Quick Start

```bash
# Build the documentation
make build

# Serve locally with live reload (opens browser)
make serve
```

The built documentation will be in `../output/`.

## Available Commands

| Command | Description |
|---------|-------------|
| `make build` | Generate opcode data and build the book |
| `make serve` | Generate data and serve with live reload |
| `make build-fast` | Build without regenerating opcode data |
| `make serve-fast` | Serve without regenerating opcode data |
| `make clean` | Remove build artifacts |
| `make data` | Only regenerate opcode data |

## Directory Structure

```
docs/book/
├── book.toml          # mdbook configuration
├── Makefile           # Build commands
├── README.md          # This file
├── src/               # Documentation source
│   ├── SUMMARY.md     # Book structure/navigation
│   ├── intro/         # Introduction & overview
│   ├── guide/         # Installation & usage
│   ├── concepts/      # Core concepts (translation, linking, etc.)
│   ├── evm/           # EVM verification & explorer
│   └── reference/     # Glossary, FAQ, contributing
└── theme/             # Custom styling
    ├── custom.css     # General book styles
    ├── rocq-highlight.css  # Rocq syntax colors
    ├── rocq-highlight.js   # Rocq syntax highlighter
    ├── explorer.css   # EVM explorer styles
    └── explorer.js    # EVM explorer logic
```

## Adding Content

1. Create/edit markdown files in `src/`
2. Update `src/SUMMARY.md` to include new pages in navigation
3. Run `make serve` to preview changes

## Rocq Code Highlighting

Use `rocq` or `coq` as the language identifier in code blocks:

````markdown
```rocq
Definition example : nat := 42.
```
````

## Deployment

Documentation is automatically deployed to GitHub Pages on push to `main` via `.github/workflows/docs.yml`.

Manual deployment:
```bash
make build
# Upload ../output/ to your hosting
```
