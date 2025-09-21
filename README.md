# Riemann-Adelic

This repository contains numerical validation code for the paper:

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Final Conditional Version V4.1)**  
Author: José Manuel Mota Burruezo  
Date: September 13, 2025  
DOI: [10.5281/zenodo.17161831](https://doi.org/10.5281/zenodo.17161831)

Technical Appendix to V4.1: Uniform Bounds, Logarithmic Lengths, and Uniqueness in the S-Finite Adelic Model
https://doi.org/10.5281/zenodo.17161831

Notebook Validation Commit: `7f191eb`

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

## Reproduction Steps
1. Install dependencies: `pip install -r requirements.txt`
2. Ensure `zeros/zeros_t1e8.txt` is present (see Data section).
3. Run validation: `python validate_explicit_formula.py --max_zeros 1000 --precision_dps 30`
4. Check results in `data/validation_results.csv`.

## Environment Setup
- **Python**: 3.10.12
- **Dependencies**: `pip install -r requirements.txt`
- **Data**: `zeros/zeros_t1e8.txt` from Odlyzko (https://www-users.cse.umn.edu/~odlyzko/zeta_tables/, 2025-09-01, Public Domain).

## Numerical Validation Parameters
- `max_zeros`: 1000
- `precision_dps`: 30
- `max_primes`: 1000
- `prime_powers`: 5
- `integration_t`: 50

## 🧠 Copilot Prompt (IA guidance)

Please suggest workflows for:

- Running `validate_explicit_formula.py` on push and saving logs.
- Executing `validation.ipynb` automatically using `nbconvert` to produce an HTML output.
- Fetching Odlyzko zero data if not present in `zeros/`.
- Archiving numerical outputs as CSV in `data/`.
- Ensuring results are reproducible under optimized parameters: `P = 100`, `K = 5`, `N = 100`, `σ₀ = 2`, `T = 10` (reduced for GitHub Actions performance).

**⚡ Performance Optimizations for CI:**

The `validation.ipynb` notebook has been optimized to run within GitHub Actions timeout limits:

- **Reduced precision**: `mp.mp.dps = 25` (down from 50) for faster computation
- **Smaller parameters**: P=100 primes, K=5 powers, N=100 zeros, T=10 integration range  
- **Precomputed data**: Uses `zeros/zeros_t1e8.txt` instead of computing zeros with `mp.zetazero()`
- **Environment variables**: CI can override parameters via `PRIME_COUNT`, `PRIME_POWERS`, `ZERO_COUNT`, `INTEGRATION_T`
- **Extended timeouts**: GitHub Actions workflow uses 30-minute notebook timeout

**Expected execution time:** ~2-10 minutes (down from >10 minutes)

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

## 🧪 Local Testing

To test the optimized notebook locally:

```bash
# Install dependencies
pip install -r requirements.txt

# Run with custom parameters
PRIME_COUNT=50 ZERO_COUNT=50 jupyter nbconvert --execute notebooks/validation.ipynb --to html

# Or test the CLI validation
python validate_explicit_formula.py --max_primes 100 --max_zeros 100
```

## Section 14: Weil Explicit Formula Details

This repository implements a numerical validation of the Weil-type explicit formula, adapted for the canonical function $D(s) \equiv \Xi(s)$ via S-finite adelic flows. The formula is:

$$
\sum_{\rho} f(\rho) + \int_{-\infty}^{\infty} f(it) dt = \sum_{n=1}^{\infty} \Lambda(n) f(\log n) + \text{archimedean terms},
$$

where:
- $\rho$ are the non-trivial zeros (from `zeros/zeros_t1e8.txt`).
- $\Lambda(n)$ is the von Mangoldt function.
- $f(u)$ is a compact-support test function (e.g., $e^{-u^2}$).
- Archimedean terms include $\Gamma(s/2) \pi^{-s/2}$ adjustments.

The validation compares the left-hand side (zeros + integral) with the right-hand side (primes + archimedean) to achieve a relative error $\leq 10^{-6}$. See `validate_explicit_formula.py` for implementation.

**Usage:**
```bash
# Run Weil explicit formula validation
python validate_explicit_formula.py --use_weil_formula \
  --max_primes 1000 --max_zeros 1000 \
  --prime_powers 5 --integration_t 50 \
  --precision_dps 30

# Check validation results
cat data/validation_results.csv
```

**Implementation Notes:**
- Requires `mpmath` for high precision and `numpy` for efficiency.
- The factor archimedean must be adjusted according to the adelic model of Burruezo (see the technical appendix of Zenodo).
- The integral is approximated numerically with `mpmath.quad`.

## Section 16: Operator Delta_S Derivation

The S-finite adelic flow constructs the operator $\Delta_S$ as follows:

- **Hilbert Space**: Defined on $L^2(\mathbb{A}_K^S / K^\times)$, where $\mathbb{A}_K^S$ is the restricted adelic ring over a finite set of places $S$.
- **Construction**:
  1. Generated by a logarithmic length operator $L$, approximated as $\Delta_S \phi(x) = - \sum_{v \in S} \frac{\partial^2}{\partial x_v^2} \phi(x) + v\text{-adic corrections}$.
  2. Ensures trace-class property via a kernel $K_S(x, y)$ from the adelic flow.
- **Eigenvalues**: $\lambda_n$ of $\Delta_S$ map to zeros of $D(s)$ via $s = \frac{1}{2} \pm i \sqrt{\lambda_n - \frac{1}{4}}$, supporting the Riemann Hypothesis.
- **Implementation**: Approximated in `validate_explicit_formula.py` using zero data, with a scaling factor $22.3 \times \frac{\text{max_zeros}}{\log(\text{max_zeros} + e)}$.

**Usage with Delta_S:**
```bash
# Run with Delta_S eigenvalue computation
python validate_explicit_formula.py --use_weil_formula \
  --max_primes 1000 --max_zeros 200 \
  --prime_powers 5 --integration_t 50 \
  --precision_dps 30

# Eigenvalues will be displayed and saved to data/validation_results.csv
```

**Theoretical Background:**
The operator $\Delta_S$ is constructed as a second-order differential operator on the adelic Hilbert space:
$$\Delta_S \phi(x) = -\sum_{v \in S} \frac{\partial^2}{\partial x_v^2} \phi(x) + \text{corrections}$$

where the corrections account for the $v$-adic structure at finite places. The eigenvalue relation $\lambda_n = \frac{1}{4} + \rho^2$ directly connects the spectrum of $\Delta_S$ to the imaginary parts $\rho$ of Riemann zeta zeros, providing a spectral interpretation of the Riemann Hypothesis.

## License
- Manuscript: CC-BY 4.0 (DOI: 10.5281/zenodo.17161831)
- Code: MIT License (see LICENSE-CODE)
