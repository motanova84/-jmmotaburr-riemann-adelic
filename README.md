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
├── notebooks/                     # Jupyter notebooks (e.g. validation.ipynb)
├── utils/
│   ├── mellin.py                 # Tools for computing Mellin transforms
│   ├── riemann_tools.py          # Riemann zeta zeros utilities
│   └── fetch_odlyzko.py          # Download Odlyzko zeros data
├── zeros/
│   └── zeros_t1e8.txt           # List of zeros at height t ~ 1e8 (from Odlyzko)
├── tests/
│   └── test_validation.py       # pytest tests for validation
├── data/                        # Output directory for results
├── validate_explicit_formula.py # Main CLI validation script
├── validate_by_height.py        # Height-specific validation script
├── requirements.txt
└── README.md
```

## 🚀 Usage

### Installation

```bash
pip install -r requirements.txt
```

### Basic Validation

1. **Explicit Formula Validation** (recommended for general use):
```bash
python validate_explicit_formula.py --max_primes 1000 --max_zeros 100
```

2. **Height-specific Validation**:
```bash
python validate_by_height.py 20
```

### Running Tests

```bash
python -m pytest tests/ -v
```

### Performance Notes

The validation scripts have been optimized for reasonable computation times:
- `validate_explicit_formula.py`: Uses reduced parameters (P≤10000, precision=15 digits)
- `validate_by_height.py`: Uses reduced parameters (P≤1000, K≤3, precision=25 digits)
- Both scripts include proper error handling and progress indicators

## 🧠 Copilot Prompt (IA guidance)

Please suggest workflows for:

- Running `validate_explicit_formula.py` on push and saving logs.
- Executing `validation.ipynb` automatically using `nbconvert` to produce an HTML output.
- Fetching Odlyzko zero data if not present in `zeros/`.
- Archiving numerical outputs as CSV in `data/`.
- Ensuring results are reproducible under `δ = 0.01`, `P = 1000`, `K = 50`, `N_Ξ = 2000`, `σ₀ = 2`, `T = 50`.

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
