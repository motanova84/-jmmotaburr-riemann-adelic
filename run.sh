#!/usr/bin/env bash
# V5 Coronación One-Command Setup and Validation
# 
# This script provides a streamlined way to set up the environment
# and run the complete V5 Coronación validation pipeline.

set -e  # Exit on any error

echo "🏆 V5 CORONACIÓN: ONE-COMMAND SETUP & VALIDATION"
echo "================================================="
echo "Setting up virtual environment and running validation..."
echo

# Check if Python 3.10-3.12 is available
python_version=$(python3 -c "import sys; print('{}.{}'.format(sys.version_info.major, sys.version_info.minor))")
echo "🐍 Detected Python version: $python_version"

if python3 -c "import sys; exit(0 if sys.version_info >= (3,13) else 1)"; then
    echo "⚠️  WARNING: Python 3.13+ detected. Recommended: Python 3.10-3.12"
    echo "   NumPy/SciPy installation may encounter issues."
    echo "   Consider using Python 3.10-3.12 for best compatibility."
    echo
fi

# Create and activate virtual environment
echo "📦 Setting up virtual environment..."
python3 -m venv .venv
source .venv/bin/activate

# Upgrade pip
echo "🔧 Upgrading pip..."
python -m pip install --upgrade pip

# Install requirements
echo "📋 Installing dependencies..."
pip install -r requirements.txt

# Fetch Odlyzko data if needed (for full precision validation)
echo "📊 Fetching Riemann zeros data..."
if ! python utils/fetch_odlyzko.py --precision t1e8; then
    echo "ℹ️  Note: Could not fetch t1e8 data. Will use t1e3 for validation."
fi

# Run V5 Coronación validation
echo
echo "🚀 Running V5 Coronación validation..."
echo "======================================"
python validate_v5_coronacion.py --precision 30 --save-certificate --verbose

echo
echo "🎉 V5 Coronación setup and validation complete!"
echo "📜 Check data/v5_coronacion_certificate.json for the proof certificate"
echo
echo "To run again later:"
echo "  source .venv/bin/activate"
echo "  python validate_v5_coronacion.py --precision 30"