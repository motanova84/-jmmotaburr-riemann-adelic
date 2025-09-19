# Riemann-Adelic

This repository contains numerical validation code for the paper:

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Definitive Revision V3.6)**  
Author: José Manuel Mota Burruezo  
Date: September 13, 2025  
DOI: [(https://doi.org/10.5281/zenodo.17116291)

Technical Appendix to V4.1: Uniform Bounds, Logarithmic Lengths, and Uniqueness in the S-Finite Adelic Model
https://zenodo.org/records/17137704

Notebook Validation Commit: `abc123`

##  Objective

Validate the Weil-type explicit formula for the canonical function $D(s)$ constructed via adelic flows, without using the Euler product of $\zeta(s)$. The validation includes:

- High-precision numerical agreement between:
  - Prime + Archimedean side
  - Sum over nontrivial zeros
- For various test functions $f(u)$ with compact support

##  Structure

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

## 🧪 Validation Parameters

### CI vs Scientific Validation

This repository implements **two levels of validation**:

**CI (Technical) Validation:**
- Parameters: `--max_primes 200 --max_zeros 200 --tolerance 1.5`
- Purpose: Verify scripts run without errors and produce reasonable results
- Expected runtime: ~2 minutes  
- Tolerance: 150% relative error (acceptable for significantly reduced parameter sets)

**Scientific Validation:**
- Parameters: `--max_primes 1000 --max_zeros 2000 --tolerance 1e-6`  
- Purpose: High-precision validation of mathematical identities
- Expected runtime: >1 hour
- Tolerance: 1e-6 relative error (documented in Appendix C and Zenodo)

> **Note**: The CI uses reduced parameters for speed and accepts higher error tolerance. Full scientific validation with tight tolerances is performed offline with larger parameter sets.

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
