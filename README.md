# Riemann-Adelic

This repository contains numerical validation code for the paper:

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Definitive Revision V3.6)**  
Author: José Manuel Mota Burruezo  
Date: September 13, 2025  
DOI: [[coming soon]  ](https://zenodo.org/uploads/17114751)
Notebook Validation Commit: `b0415ac` (✅ Fixed and Working)

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

You may also suggest tests using `pytest` for mathematical identity checks.

## 🚀 Quick Start

The repository is now fully functional. To run the validation:

### 1. Install Dependencies
```bash
pip install -r requirements.txt
```

### 2. Run Main Validation
```bash
python validate_explicit_formula.py --delta 0.01 --max_primes 1000 --max_zeros 2000 --test_functions f1 f2 f3
```

### 3. Run Jupyter Notebook
```bash
jupyter nbconvert --to html --execute notebooks/validation.ipynb --output-dir docs/ --output validation.html
```

### 4. Run Tests
```bash
pytest tests/test_validation.py -v
```

### 5. Height-Specific Validation
```bash
python validate_by_height.py 100  # Test at height t=100
```

All outputs are saved to `data/` directory as CSV files. The notebook generates HTML output in `docs/`.

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
