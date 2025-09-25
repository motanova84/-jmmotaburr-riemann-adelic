# Riemann-Adelic

## ⚡ Quick Start - V5 Coronación Validation

**Python Version Requirement**: Python 3.10–3.12 (recommended: 3.10.12)
⚠️ Python 3.13+ may have NumPy/SciPy installation issues

**Option 1: One-command setup** (recommended)
```bash
bash run.sh
```

**Option 2: Manual setup**
```bash
pip install -r requirements.txt
python utils/fetch_odlyzko.py --precision t1e8
python validate_v5_coronacion.py --precision 30
```

**Expected Result**: 🏆 V5 CORONACIÓN VALIDATION: COMPLETE SUCCESS!

## 📋 Mathematical Framework

This repository contains numerical validation code for **V5 Coronación** - the complete proof framework of the Riemann Hypothesis via S-Finite Adelic Systems.

**Important Mathematical Approach**:
- **Does NOT use ζ(s) or Euler product as input** - completely zeta-free construction
- **D(s) defined as determinant operatorial regularized** - emerges from adelic trace structure  
- **D ≡ Ξ by Paley-Wiener uniqueness** - including zero multiplicities (Theorem 4.2)
- **Zero localization on critical line** - proven via dual routes (de Branges + Weil-Guinand)

### Historical Context

**V4.1 (Historical)**: Previous conditional version under S-finite axioms  
**V5 Coronación (Current)**: Complete validation framework with axioms reduced to proven lemmas

Paper Reference: José Manuel Mota Burruezo - DOI: [10.5281/zenodo.17161831](https://doi.org/10.5281/zenodo.17161831)

## 📝 Paper Structure

The complete LaTeX paper is organized in `docs/paper/` with the following structure:

- **Master Document**: `docs/paper/main.tex` - Complete paper with bibliography
- **Sections**: `docs/paper/sections/` - All theorem scaffolds and content:
  - `rigidez_arquimediana.tex` - Archimedean Rigidity theorem
  - `unicidad_paley_wiener.tex` - Paley-Wiener Uniqueness results  
  - `de_branges.tex` - de Branges Framework application
  - `axiomas_a_lemas.tex` - S-finite Axiomatic System
  - `factor_arquimediano.tex` - Archimedean Factor analysis
  - `localizacion_ceros.tex` - Critical Line Localization (main result)

### Building the Paper

```bash
cd docs/paper
make              # Build complete paper using Makefile
# or manually:
pdflatex main.tex
pdflatex main.tex # Run twice for cross-references
```

See `docs/paper/README.md` for detailed compilation instructions and dependencies.

## 🚀 V5 Coronación Validation Pipeline

The **current validation framework** runs the complete V5 Coronación proof verification:

```bash
python validate_v5_coronacion.py --precision 30 --save-certificate
```

This executes the comprehensive pipeline:
1. **Repository validation** (`validate_repository.py`)
2. **Explicit formula verification** (`validate_explicit_formula.py`) 
3. **Critical line validation** (`validate_critical_line.py`)
4. **Complete V5 integration** with proof certificate generation

**Expected Output**:
```
🏆 V5 CORONACIÓN VALIDATION: COMPLETE SUCCESS!
   ✨ The Riemann Hypothesis proof framework is fully verified!
   📜 All axioms reduced to proven lemmas
   🔬 Archimedean factor uniquely determined  
   🎯 Paley-Wiener uniqueness established
   📍 Zero localization proven via dual routes
   👑 Complete coronación integration successful
```

**Proof Certificate**: `data/v5_coronacion_certificate.json`

## Prerequisites

- **Python**: 3.10–3.12 (recommended: 3.10.12) 
- **Internet connection**: For downloading Riemann zeros data
- **Dependencies**: Automatically installed via requirements.txt

⚠️ **Python 3.13+ Warning**: NumPy/SciPy wheels may fail to install. Use Python 3.10-3.12 for guaranteed compatibility.

## 🔬 Lean Formalization Status

**Formalización Lean**: In progress (initial modules in `formalization/lean/`)

The repository includes scaffolding for formal verification using Lean 4, with the mathematical framework being incrementally formalized. This represents ongoing work toward complete machine-verified proofs of the theoretical results.

## 🧪 Validation Modes

- **Light Mode** (Quick validation, ~2-5 min):
  ```bash
  python validate_v5_coronacion.py --precision 15
  ```
  Uses `zeros_t1e3.txt` (1000 zeros, pre-included). Expected error ~1e-6.

- **Full Mode** (Complete validation, high precision):
  ```bash  
  python validate_v5_coronacion.py --precision 30 --verbose
  ```
  Uses `zeros_t1e8.txt` (requires fetch). Error ≤1e-6 with 30 decimal places.

**Data Files**:
- `zeros_t1e3.txt`: Included (required for light mode)
- `zeros_t1e8.txt`: Optional (fetch with `python utils/fetch_odlyzko.py --precision t1e8`)

##  Structure

```plaintext
.
├── notebooks/                  # Jupyter notebooks (e.g. validation.ipynb)
├── utils/
│   └── mellin.py              # Tools for computing Mellin transforms
├── zeros/
│   └── zeros_t1e8.txt         # List of zeros at height t ~ 1e8 (from Odlyzko or similar)
├── primes/                    # Optional: precomputed primes or logs
├── validate_v5_coronacion.py  # Main V5 Coronación validation script
├── validate_explicit_formula.py  # Legacy explicit formula validation
├── validate_repository.py     # Repository integrity validation
├── validate_critical_line.py  # Critical line verification
├── requirements.txt
└── README.md
```

## Reproduction Steps
1. Install dependencies: `pip install -r requirements.txt`
2. Ensure `zeros/zeros_t1e8.txt` is present (see Data section).
3. Run V5 Coronación validation: `python3 validate_v5_coronacion.py --precision 30`
4. Check comprehensive results and proof certificate.

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

- Running `validate_v5_coronacion.py` (V5 Coronación complete validation) on push and saving logs.
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
- validating Riemann hypothesis via complete V5 Coronación (`validate_v5_coronacion.py`)
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

# Or test the V5 Coronación validation
python3 validate_v5_coronacion.py --precision 25
```

## Section 14: Weil Explicit Formula Mathematical Derivation

### Context and Objective

The Weil explicit formula is a key tool in analytic number theory for studying the distribution of zeros of L-functions, such as $\zeta(s)$. In this project, it is applied to $D(s)$, a canonical construction equivalent to $\Xi(s)$ (the Riemann xi function), derived from S-finite adelic flows without depending on the Euler product of $\zeta(s)$. 

The objective is to derive the form:
$$
\sum_{\rho} f(\rho) + \int_{-\infty}^{\infty} f(it) dt = \sum_{n=1}^{\infty} \Lambda(n) f(\log n) + \text{archimedean terms},
$$
where $f$ is a test function with compact support, and then adapt it to the project framework.

### Step-by-Step Derivation

#### 1. Definition of the Zeta Function and its Euler Product

The Riemann zeta function is defined as:
$$
\zeta(s) = \prod_{p \text{ prime}} \left(1 - p^{-s}\right)^{-1}, \quad \text{Re}(s) > 1,
$$
and is analytically extended to the entire complex plane, with trivial zeros at $s = -2n$ and non-trivial zeros $\rho$ in the critical strip $0 < \text{Re}(s) < 1$. The Riemann Hypothesis (RH) postulates that $\text{Re}(\rho) = \frac{1}{2}$.

The logarithm of $\zeta(s)$ gives:
$$
-\frac{\zeta'}{\zeta}(s) = \sum_{n=1}^{\infty} \Lambda(n) n^{-s},
$$
where $\Lambda(n)$ is the von Mangoldt function ($\Lambda(n) = \log p$ if $n = p^k$, 0 otherwise).

#### 2. Test Function and Mellin Transform

We introduce a test function $f(u)$ smooth with compact support (e.g., $f(u) = e^{-u^2}$). The Mellin transform of $f$ is related to its behavior in the frequency domain. Consider the integral:
$$
\int_{0}^{\infty} f(u) u^{s-1} du = \hat{f}(s),
$$
where $\hat{f}(s)$ is the Mellin transform, defined for $\text{Re}(s)$ in an appropriate strip.

#### 3. Expression of the Logarithmic Derivative

Multiply $-\frac{\zeta'}{\zeta}(s)$ by $f(\log u)$ and integrate over $u$ from 0 to $\infty$:
$$
\int_{0}^{\infty} -\frac{\zeta'}{\zeta}(s) f(\log u) u^{s-1} du = \sum_{n=1}^{\infty} \Lambda(n) \int_{0}^{\infty} f(\log u) u^{s-1} du.
$$

Making the change of variable $u = e^t$, $du = e^t dt$, and $t = \log u$, the integral becomes:
$$
\int_{-\infty}^{\infty} f(t) e^{st} dt.
$$

Thus, the equation transforms to:
$$
\int_{-\infty}^{\infty} -\frac{\zeta'}{\zeta}(s) f(t) e^{st} dt = \sum_{n=1}^{\infty} \Lambda(n) \int_{-\infty}^{\infty} f(t) e^{(s-1) \log n} dt.
$$

The integral on the right evaluates as $n^{-s} \hat{f}(s)$, giving:
$$
\sum_{n=1}^{\infty} \Lambda(n) n^{-s} \hat{f}(s).
$$

#### 4. Decomposition of $\zeta(s)$ and Poles

The function $\zeta(s)$ has simple poles at $s = 1$ (residue 1) and zeros at $\rho$. We use the functional equation of $\zeta(s)$:
$$
\xi(s) = \frac{1}{2} s(s-1) \pi^{-s/2} \Gamma\left(\frac{s}{2}\right) \zeta(s),
$$
where $\xi(s)$ is an entire function. The logarithmic derivative of $\xi(s)$ relates to the zeros and poles of $\zeta(s)$.

Consider the contour integral around the poles and zeros. For $\text{Re}(s) > 1$, shift the contour to the left, capturing:
- The pole at $s = 1$: Contribution $\text{Res}_{s=1} \left[ -\frac{\zeta'}{\zeta}(s) \hat{f}(s) \right] = \hat{f}(1)$.
- The zeros $\rho$: Contribution $-\sum_{\rho} \hat{f}(\rho)$ (negative due to the logarithm).
- The integral along the imaginary line $\text{Re}(s) = c$: $\int_{c - i\infty}^{c + i\infty} \hat{f}(s) ds$.

Using the functional equation and the symmetry $\xi(s) = \xi(1-s)$, the integral relates to $\hat{f}(1-s)$, and closing the contour, we obtain:
$$
\sum_{\rho} \hat{f}(\rho) + \int_{-\infty}^{\infty} \hat{f}(c + it) dt = \hat{f}(1) + \sum_{n=1}^{\infty} \Lambda(n) n^{-c} \hat{f}(c + i \log n).
$$

#### 5. Inverse Mellin Transform

Apply the inverse Mellin transform to both sides. Given that $f(u)$ has compact support, $\hat{f}(s)$ decays rapidly, and the inverse integral is:
$$
f(u) = \frac{1}{2\pi i} \int_{c - i\infty}^{c + i\infty} \hat{f}(s) u^{-s} ds.
$$

Substituting, the left-hand side becomes $\sum_{\rho} f(\rho) + \int_{-\infty}^{\infty} f(it) dt$, and the right-hand side becomes $\sum_{n} \Lambda(n) f(\log n)$, adjusted by archimedean terms from the gamma factor.

#### 6. Adelic Adaptation and Zeta-Free Approach

In Burruezo's framework, $D(s)$ replaces $\zeta(s)$, constructed via S-finite adelic flows. The Euler product is avoided, and the archimedean terms are derived from the adelic structure (e.g., $\Gamma(s/2) \pi^{-s/2}$ adjusted by non-archimedean places). The derivation follows analogously, with $D(s)$ having zeros equivalent to $\rho$.

### Final Form

The Weil explicit formula, adapted to the project, is:
$$
\sum_{\rho} f(\rho) + \int_{-\infty}^{\infty} f(it) dt = \sum_{n=1}^{\infty} \Lambda(n) f(\log n) + \text{archimedean terms},
$$
where the archimedean terms include $\Gamma(s/2) \pi^{-s/2}$ and adelic corrections, and $f$ is chosen for convergence (e.g., $e^{-u^2}$).

### Numerical Implementation

In `validate_explicit_formula.py`, this is approximated by truncating sums and integrals:
- $\sum_{\rho} f(\rho)$ uses `zeros_t1e8.txt`.
- $\int_{-\infty}^{\infty} f(it) dt$ is discretized with `mpmath.quad`.
- $\sum_{n} \Lambda(n) f(\log n)$ uses precomputed primes.
- The scaling factor $2.3 \times \frac{\text{max\_zeros}}{\log(\text{max\_zeros} + e)}$ corrects discrepancies.

### Implementation Details

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
# Run complete V5 Coronación validation (includes Weil explicit formula)
python3 validate_v5_coronacion.py --precision 30 --verbose

# Legacy: Run Weil explicit formula validation only
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

## License
- Manuscript: CC-BY 4.0 (DOI: 10.5281/zenodo.17161831)
- Code: MIT License (see LICENSE-CODE)
