# Makefile for Riemann-Adelic Formal Verification
# Builds and verifies all Lean 4 formal content

.PHONY: all proof clean help

# Default target
all: proof

# Proof target: build and verify all Lean formalization
proof:
	@echo "Building Lean 4 formalization..."
	cd formalization/lean && lake build
	@echo "✓ Proof verification complete!"

# Clean build artifacts
clean:
	@echo "Cleaning Lean build artifacts..."
	cd formalization/lean && lake clean
	@echo "✓ Clean complete!"

# Help target
help:
	@echo "Available targets:"
	@echo "  proof     - Build and verify all Lean 4 formal proofs (default)"
	@echo "  clean     - Clean build artifacts"
	@echo "  help      - Show this help message"
	@echo ""
	@echo "Docker usage (reproducible build):"
	@echo "  docker run --rm -v \"\$$PWD\":/work -w /work leanprovercommunity/lean:4.5.0 /bin/bash -lc \"make proof\""
	@echo ""
	@echo "Nix usage (reproducible build):"
	@echo "  nix develop --command make proof"
