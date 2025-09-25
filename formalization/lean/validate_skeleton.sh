#!/bin/bash

# Validation script for RH Lean4 Skeleton V5.1
# Checks that the skeleton compiles without errors

echo "🔍 Validating Riemann Hypothesis Lean4 Skeleton V5.1..."
echo "======================================================="

# Check if lean is available
if ! command -v lean &> /dev/null; then
    echo "❌ Lean 4 not found. Please install Lean 4 toolchain first."
    echo "   Visit: https://leanprover.github.io/lean4/doc/quickstart.html"
    exit 1
fi

# Check if lake is available  
if ! command -v lake &> /dev/null; then
    echo "❌ Lake not found. Please ensure Lean 4 installation is complete."
    exit 1
fi

echo "✅ Lean 4 toolchain found"

# Navigate to Lean directory
cd "$(dirname "$0")"

echo "📂 Current directory: $(pwd)"

# Check lake configuration
if [ ! -f "lakefile.lean" ]; then
    echo "❌ lakefile.lean not found"
    exit 1
fi

echo "✅ Lake configuration found"

# Build the project
echo "🔨 Building Lean project..."
lake build

if [ $? -eq 0 ]; then
    echo "✅ Build successful!"
    echo ""
    echo "🎉 RH Skeleton V5.1 validation complete!"
    echo "   All modules compile correctly."
    echo "   Ready for community implementation."
    echo ""
    echo "🚀 Next steps:"
    echo "   1. Replace 'sorry' proofs with actual implementations"
    echo "   2. Implement canonical determinant D(s)"
    echo "   3. Complete axioms A1, A2, A4 as lemmas"
    echo "   4. Implement de Branges localization"
    echo "   5. Achieve QED! ✨"
else
    echo "❌ Build failed. Please check the error messages above."
    echo "   This is expected if dependencies are missing or"
    echo "   if there are syntax errors in the skeleton."
    exit 1
fi