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

## 📂 Structure

```plaintext
.
├── notebooks/                  # Jupyter notebooks (e.g. validation.ipynb)
├── utils/
│   └── mellin.py              # Tools for computing Mellin transforms
├── zeros/
│   └── zeros_t1e8.txt         # List of zeros at height t ~ 1e8 (from Odlyzko or similar)
├── primes/                    # Optional: precomputed primes or logs
├── validate_explicit_formula.py  # Main CLI validation script
├── requirements.txt
└── README.md
```

## 🧠 Copilot Prompt (IA guidance)

Please suggest workflows for:

- Running `validate_explicit_formula.py` on push and saving logs.
- Executing `validation.ipynb` automatically using `nbconvert` to produce an HTML output.
- Fetching Odlyzko zero data if not present in `zeros/`.
- Archiving numerical outputs as CSV in `data/`.
- Ensuring results are reproducible under `δ = 0.01`, `P = 1000`, `K = 50`, `N_Ξ = 2000`, `σ₀ = 2`, `T = 50`.

## 🚀 Quick Start

### Running Validation

```bash
# 1. Ensure Odlyzko zeros data is available
python utils/fetch_odlyzko.py

# 2. Run validation with specified parameters (δ=0.01, P=1000, K=50, N_Ξ=2000, σ₀=2, T=50)
python validate_explicit_formula.py

# 3. Run comprehensive test suite
python -m pytest tests/ -v

# 4. Execute notebook and export HTML (optimized for CI)
python utils/execute_notebook.py --fast
```

### Outputs

- **CSV Results**: `data/validation_results_*.csv` - Numerical validation results
- **Logs**: `logs/validation_*.log` - Detailed computation logs  
- **HTML Reports**: `docs/validation.html` - Notebook execution results
- **Test Reports**: Pytest generates detailed mathematical validation tests

## 🔬 Validation Features

- **Reproducible Parameters**: δ=0.01, P=1000, K=50, N_Ξ=2000, σ₀=2, T=50
- **Comprehensive Logging**: Timestamped logs with detailed computation tracking
- **Mathematical Identity Tests**: 8 comprehensive pytest tests for validation
- **Automated Workflows**: GitHub Actions for CI/CD validation
- **Data Management**: Automatic Odlyzko zeros fetching and validation

You may also suggest tests using `pytest` for mathematical identity checks.

## 🤖 Quick Copilot Integration

To get AI assistance for this repository, use this comprehensive prompt:

```
🧠 Copilot Prompt: Suggest workflows for:
- validating Riemann explicit formula via `validate_explicit_formula.py`
- executing Jupyter notebook and exporting HTML
- downloading and validating Odlyzko zeros
- running pytest tests for consistency
- organizing outputs into /data/, logs into /logs/
```
