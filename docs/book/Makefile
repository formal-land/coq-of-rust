.PHONY: all build serve clean data

# Default target
all: build

# Generate opcode data from Rocq files
data:
	python3 ../scripts/generate_opcode_data.py

# Build the documentation
build: data
	mdbook build

# Serve documentation with live reload
serve: data
	mdbook serve --open

# Clean build artifacts
clean:
	rm -rf ../output
	rm -f ../data/opcodes.json

# Build without regenerating data (faster for iterating on docs)
build-fast:
	mdbook build

# Serve without regenerating data
serve-fast:
	mdbook serve --open

# Test that the book builds successfully
test:
	mdbook test
