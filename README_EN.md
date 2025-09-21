# Riemann-Adelic

This repository contains numerical validation code for the paper:

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Final Conditional Version V4.1)**  
Author: José Manuel Mota Burruezo  
Date: September 13, 2025  
DOI: [10.5281/zenodo.17161831](https://doi.org/10.5281/zenodo.17161831)

Technical Appendix to V4.1: Uniform Bounds, Logarithmic Lengths, and Uniqueness in the S-Finite Adelic Model  
https://doi.org/10.5281/zenodo.17161831

## Objective

Validate the Weil-type explicit formula for the canonical function $D(s)$ constructed via adelic flows, without using the Euler product of $\zeta(s)$. The validation includes:

- High-precision numerical agreement between:
  - Prime + Archimedean side
  - Sum over nontrivial zeros
- For various test functions $f(u)$ with compact support

## Structure

```plaintext
.
├── notebooks/                  # Jupyter notebooks (e.g., validation.ipynb)
├── utils/
│   └── mellin.py              # Tools for computing Mellin transforms
├── zeros/
│   └── zeros_t1e8.txt         # List of zeros at height t ~ 1e8
├── tests/                     # Automated tests with pytest
├── validate_explicit_formula.py  # Main CLI validation script
├── requirements.txt           # Python dependencies
├── environment.yml            # Conda environment specification  
└── README.md
```

## Installation & Setup

### Option 1: Using pip
```bash
pip install -r requirements.txt
```

### Option 2: Using conda
```bash
conda env create -f environment.yml
conda activate riemann-adelic
```

## Reproduction Steps
1. Install dependencies (see above)
2. Ensure `zeros/zeros_t1e8.txt` is present (see Data section)
3. Run validation: `python validate_explicit_formula.py --max_zeros 1000 --precision_dps 30`
4. Check results in `data/validation_results.csv`

## Environment Setup
- **Python**: 3.11+ (recommended)
- **Dependencies**: See `requirements.txt` or `environment.yml`
- **Data**: `zeros/zeros_t1e8.txt` from Odlyzko (https://www-users.cse.umn.edu/~odlyzko/zeta_tables/, 2025-09-01, Public Domain)

## Numerical Validation Parameters
- `max_zeros`: 1000
- `precision_dps`: 30
- `max_primes`: 1000
- `prime_powers`: 5
- `integration_t`: 50

## Testing

Run automated tests with:
```bash
pytest tests/ -v
```

## Weil Explicit Formula Mathematical Derivation

### Implementation Details

This repository implements a numerical validation of the Weil-type explicit formula, adapted for the canonical function $D(s) \\equiv \\Xi(s)$ via S-finite adelic flows. The formula is:

$$
\\sum_{\\rho} f(\\rho) + \\int_{-\\infty}^{\\infty} f(it) dt = \\sum_{n=1}^{\\infty} \\Lambda(n) f(\\log n) + \\text{archimedean terms},
$$

where:
- $\\rho$ are the non-trivial zeros (from `zeros/zeros_t1e8.txt`)
- $\\Lambda(n)$ is the von Mangoldt function
- $f(u)$ is a compact-support test function (e.g., $e^{-u^2}$)
- Archimedean terms include $\\Gamma(s/2) \\pi^{-s/2}$ adjustments

The validation compares the left-hand side (zeros + integral) with the right-hand side (primes + archimedean) to achieve a relative error $\\leq 10^{-6}$.

**Usage:**
```bash
# Run Weil explicit formula validation
python validate_explicit_formula.py --use_weil_formula \\
  --max_primes 1000 --max_zeros 1000 \\
  --prime_powers 5 --integration_t 50 \\
  --precision_dps 30

# Check validation results
cat data/validation_results.csv
```

## License
- Manuscript: CC-BY 4.0 (DOI: 10.5281/zenodo.17161831)
- Code: MIT License (see LICENSE-CODE)

## Contact
- José Manuel Mota Burruezo: institutoconciencia@proton.me
- GitHub repository: https://github.com/motanova84/-jmmotaburr-riemann-adelic