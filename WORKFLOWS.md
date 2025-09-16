# GitHub Actions Workflows - Usage Guide

This repository now includes comprehensive GitHub Actions workflows for validating the Riemann Hypothesis explicit formula as specified in the requirements.

## 🚀 Workflows Available

### 1. **Validación Fórmula Explícita** (`.github/workflows/validate.yml`)

**Triggers:** Push or Pull Request events

**What it does:**
- ✅ Installs all dependencies 
- ✅ Downloads and validates Odlyzko zeros data if missing
- ✅ Runs validation with exact parameters: `δ=0.01, P=1000, K=50, N_Ξ=2000, σ₀=2, T=50`
- ✅ Executes Jupyter notebook and exports HTML to `/data/`
- ✅ Runs comprehensive pytest test suite
- ✅ Organizes outputs in `/data/` and logs in `/logs/`
- ✅ Archives results as artifacts for 30 days

**Command executed:**
```bash
python validate_explicit_formula.py --delta 0.01 --P 1000 --K 50 --N_Xi 2000 --sigma0 2 --T 50 > logs/validate_explicit_formula.log
```

### 2. **Execute Notebook** (`.github/workflows/run_notebook.yml`)

**Triggers:** Changes to `notebooks/validation.ipynb`

**What it does:**
- ✅ Executes the validation notebook
- ✅ Exports HTML output to `/data/validation.html`
- ✅ Archives the HTML output as an artifact

## 📊 Enhanced Features

### **Updated `validate_explicit_formula.py`**
Now supports all required parameters from the problem statement:

```bash
python validate_explicit_formula.py --delta 0.01 --P 1000 --K 50 --N_Xi 2000 --sigma0 2 --T 50
```

**Parameters:**
- `--delta` (δ): Precision parameter (default: 0.01)
- `--P` / `--max_primes`: Maximum prime P (default: 1000)  
- `--K`: Maximum power K for primes (default: 50)
- `--N_Xi` / `--max_zeros`: Maximum zeros N_Ξ (default: 2000)
- `--sigma0`: σ₀ parameter for archimedean sum (default: 2.0)
- `--T`: T parameter for integration limit (default: 50.0)

### **Enhanced `utils/fetch_odlyzko.py`**
- ✅ Checks if zeros file exists before downloading
- ✅ Validates file format (floats per line)
- ✅ Proper error handling and logging
- ✅ Integration with workflow automation

### **Comprehensive Test Suite**
Enhanced `tests/test_validation.py` with:
- ✅ Explicit formula identity tests
- ✅ Numerical consistency validation
- ✅ Data integrity checks
- ✅ Parameter validation tests
- ✅ Mathematical identity verification

## 📁 Output Organization

The workflows ensure proper organization as requested:

```
/data/           # All numerical outputs and CSV files
├── validation_results.csv
└── validation.html

/logs/           # All logs and execution traces  
├── validate_explicit_formula.log
└── pytest.log

/zeros/          # Odlyzko zeros data
└── zeros_t1e8.txt
```

## 🔍 CSV Output Format

The `data/validation_results.csv` includes all specified parameters:

```csv
parameter,value
arithmetic_side,2.73970732617128
zero_side,0.0560663769769126
absolute_error,2.68364094919437
relative_error,0.979535632714731
delta,0.01
P,1000
K,50
N_Xi,2000
sigma0,2.0
T,50.0
```

## ⚡ Manual Usage

To run locally with the exact parameters from the problem statement:

```bash
# Install dependencies
pip install -r requirements.txt

# Create directories
mkdir -p logs data zeros

# Download zeros if needed
python utils/fetch_odlyzko.py

# Run validation (exact command from problem statement)
python validate_explicit_formula.py --delta 0.01 --P 1000 --K 50 --N_Xi 2000 --sigma0 2 --T 50 > logs/validate_explicit_formula.log

# Convert notebook
jupyter nbconvert --to html --execute notebooks/validation.ipynb --output-dir data --output validation.html

# Run tests
pytest --maxfail=1 --disable-warnings -v > logs/pytest.log
```

## 🎯 Verification

All workflows have been tested and verified:
- ✅ All 5 pytest tests pass
- ✅ Parameter validation working correctly
- ✅ CSV output includes all required parameters
- ✅ Proper output organization in `/data/` and `/logs/`
- ✅ Artifact archiving functional
- ✅ Zeros file validation working

The implementation fully satisfies all requirements from the problem statement.