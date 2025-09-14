# Riemann-Adelic

This repository contains numerical validation code for the paper:

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Definitive Revision V3.6)**  
Author: José Manuel Mota Burruezo  
Date: September 13, 2025  
DOI: [(https://doi.org/10.5281/zenodo.17116291)
Notebook Validation Commit: `abc123`

## 🧪 Objective

Validate the Weil-type explicit formula for the canonical function $D(s)$ constructed via adelic flows, without using the Euler product of $\zeta(s)$. The validation includes:

- High-precision numerical agreement between:
  - Prime + Archimedean side
  - Sum over nontrivial zeros
- For various test functions $f(u)$ with compact support
- **Scientific rigor through falsification testing** (perturbation analysis)
- **Reproducible results with specified parameters**: δ=0.01, P=1000, T=50

## 📂 Structure

```plaintext
.
├── notebooks/                  # Jupyter notebooks (e.g. validation.ipynb)
├── utils/
│   ├── mellin.py              # Tools for computing Mellin transforms
│   ├── riemann_tools.py       # Riemann zeta utilities
│   └── fetch_odlyzko.py       # Download Odlyzko zero data
├── zeros/
│   └── zeros_t1e8.txt         # List of zeros at height t ~ 1e8 (from Odlyzko or similar)
├── data/                      # CSV output files from validation runs
├── logs/                      # Execution logs
├── tests/                     # Pytest test suite
├── validate_explicit_formula.py  # Main CLI validation script (enhanced with CSV output)
├── perturb_test.py            # NEW: Falsification testing via perturbations
├── demo_validation.py         # Quick demo with minimal parameters
├── validate_by_height.py      # Validation at specific zero heights
├── requirements.txt
└── README.md
```

## 🔬 New Features (Scientific Rigor)

### Perturbation Testing (`perturb_test.py`)
Implements falsification tests to demonstrate the method is **"alive and scientific, not dogmatic"**:

- **Perturb log q_v**: Add noise to prime logarithms
- **Perturb kernels**: Modify digamma functions and Archimedean terms  
- **Perturb symmetry**: Break the explicit formula symmetry artificially

Expected result: Perturbations should **break** the explicit formula balance, showing high sensitivity.

```bash
# Run perturbation tests
python perturb_test.py --test-type all --P 1000 --T 50 --delta 0.01

# Test specific perturbation
python perturb_test.py --test-type prime_logs --delta 0.1
```

### Enhanced Validation with CSV Output
The main validation script now supports:

- **Command-line arguments** for reproducible testing
- **CSV output** of numerical results  
- **Multiple test functions**: f1, f2, f3, truncated_gaussian
- **Specified parameters**: P=1000, T=50, tolerance=1e-6

```bash
# Run with problem statement parameters
python validate_explicit_formula.py --P 1000 --T 50 --tolerance 1e-6

# Test multiple functions with CSV output
python validate_explicit_formula.py --functions f1 f2 f3 --output data/results.csv
```

## 🚀 Quick Start

For immediate verification with fast parameters:

```bash
# Quick demo (runs in seconds)
python demo_validation.py

# Quick test with pytest
PYTHONPATH=. pytest tests/test_validation.py -v
```

## 🧠 Copilot Prompt (IA guidance)

Please suggest workflows for:

- Running `validate_explicit_formula.py` on push and saving logs.
- Executing `validation.ipynb` automatically using `nbconvert` to produce an HTML output.
- Fetching Odlyzko zero data if not present in `zeros/`.
- Archiving numerical outputs as CSV in `data/`.
- Ensuring results are reproducible under `δ = 0.01`, `P = 1000`, `K = 50`, `N_Ξ = 2000`, `σ₀ = 2`, `T = 50`.
- **NEW**: Running perturbation tests for scientific rigor validation.

You may also suggest tests using `pytest` for mathematical identity checks.

## 🤖 Quick Copilot Integration

To get AI assistance for this repository, use this comprehensive prompt:

```
🧠 Copilot Prompt: Suggest workflows for:
- validating Riemann explicit formula via `validate_explicit_formula.py`
- executing Jupyter notebook and exporting HTML
- downloading and validating Odlyzko zeros
- running pytest tests for consistency
- running perturbation tests for scientific rigor (perturb_test.py)
- organizing outputs into /data/, logs into /logs/
```
