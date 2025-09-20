#!/bin/bash
# Setup script for Riemann-Adelic repository

set -e

echo "🚀 Setting up Riemann-Adelic environment..."

# Create virtual environment
echo "📦 Creating virtual environment..."
python -m venv env

# Activate virtual environment
echo "🔄 Activating virtual environment..."
source env/bin/activate

# Install dependencies
echo "📥 Installing dependencies..."
pip install -r requirements.txt

# Create necessary directories
echo "📁 Creating directories..."
mkdir -p zeros
mkdir -p data
mkdir -p logs

# Check if zeros data exists
if [ -f zeros/zeros_t1e8.txt ]; then
    echo "✅ zeros_t1e8.txt already exists."
else
    echo "⚠️  zeros_t1e8.txt not found."
    echo "   You may need to download it manually from:"
    echo "   https://www-users.cse.umn.edu/~odlyzko/zeta_tables/"
fi

echo "✅ Environment setup complete!"
echo "🔧 To activate the environment, run: source env/bin/activate"
echo "🧪 To test the setup, run: python validate_explicit_formula.py --max_zeros 100"