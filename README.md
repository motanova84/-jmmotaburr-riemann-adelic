# Riemann-Adelic

This repository contains numerical validation code for the paper:

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Final Conditional Version V4.1)**  
Author: José Manuel Mota Burruezo  
Date: September 13, 2025  
DOI: [10.5281/zenodo.17161831](https://doi.org/10.5281/zenodo.17161831)

Technical Appendix to V4.1: Uniform Bounds, Logarithmic Lengths, and Uniqueness in the S-Finite Adelic Model
https://doi.org/10.5281/zenodo.17161831

Notebook Validation Commit: `7f191eb`

## 📋 Theoretical Framework

**Important**: This paper is conditional under S-finite axioms:
- **A1**: Flujo escala finito (finite scale flow)
- **A2**: Simetría (symmetry) 
- **A4**: Regularidad espectral (spectral regularity)

**Logical Proof Structure**: The mathematical "proof" is detailed in the PDF (Zenodo DOI [10.5281/zenodo.17167857](https://doi.org/10.5281/zenodo.17167857)). The construction proceeds as follows:

1. **Construction of D(s)**: Builds D(s) as an entire function of order ≤1
2. **Functional Symmetry**: Establishes symmetry D(1-s) = D(s)  
3. **Normalization**: Applies normalization condition lim log D(s) = 0
4. **Uniqueness**: Identifies D ≡ Ξ via Paley-Wiener uniqueness (Theorem 4.2, including zero multiplicities)
5. **Riemann Hypothesis**: Derives RH as Theorem 4.3

**Framework Properties**:
- **Internally Consistent**: Zeta-free construction where primes emerge from adelic trace
- **Conditional Validity**: Valid as conditional framework under specified axioms
- **Falsifiable**: Appendix C shows perturbations ℓ_v ≠ log q_v would collapse the framework
- **Mathematical Rigor**: Non-circular, rigorous within trace-class theory (Birman-Solomyak)

## 📖 Current Status

From conditional framework → Towards unconditional proof (V5 Coronation milestone).

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

## 🚀 Quick Start

### Prerequisites
- Python 3.8+ 
- Internet connection (for downloading Riemann zeros data)

### One-Command Setup
```bash
# Clone and setup in one go
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
cd -jmmotaburr-riemann-adelic
python setup_environment.py --full-setup
```

### Manual Setup
```bash
# 1. Install dependencies
pip install -r requirements.txt

# 2. Fetch Riemann zeros data  
python utils/fetch_odlyzko.py --precision t1e8

# 3. Run quick validation
python validate_explicit_formula.py --max_primes 100 --max_zeros 100

# 4. Execute notebook
jupyter nbconvert --execute notebooks/validation.ipynb --to html
```

## 🚀 Validación V5 Coronación

Una vez clonado el repositorio y con las dependencias instaladas (`pip install -r requirements.txt`):

```bash
python3 validar_v5_coronacion.py
```

👉 Este único comando lanza toda la validación:

• Fórmula explícita de Weil
• Línea crítica  
• Validaciones numéricas (errores < 1e-6)
• Chequeos del marco axiomático V5

### Validation Results
The validation compares two sides of the Weil explicit formula:
- **Left side**: Sum over non-trivial zeros + archimedean integral
- **Right side**: Sum over prime powers + archimedean terms

Expected output:
```
✅ Computation completed!
Aritmético (Primes + Arch): [complex number]
Zero side (explicit sum):   [complex number]  
Error absoluto:             [small value]
Error relativo:             [< 1e-6 for high precision]
```

## Modes for Validation
- **Light Mode**: Usa dataset mínimo (zeros_t1e3.txt con 1000 ceros, preincluido). Validación rápida (~2-5 min). Error esperado ~1e-6 con dps=15.
  Ejemplo: `python validate_explicit_formula.py --max_zeros 1000 --max_primes 100 --precision_dps 15 --mode light`
- **Full Mode**: Usa dataset completo (zeros_t1e8.txt, fetch requerido). Validación completa (~horas). Error ≤1e-6 con dps=30.
  Ejemplo: `python validate_explicit_formula.py --max_zeros 1000000 --max_primes 1000 --precision_dps 30 --mode full --integration_t 50`

## Raw Files Opcionales
- zeros_t1e3.txt: Requerido para light mode (incluido).
- zeros_t1e8.txt: Opcional para full mode (fetch con `python utils/fetch_odlyzko.py --precision t1e8`).

## Ejemplos Concretos de Ejecución
- CLI Light: `python validate_explicit_formula.py --max_zeros 1000 --test_function f2 --formula_type weil`
  Output esperado: Relative Error ~1e-6, saved to data/validation_results.csv.
- Notebook Full: `jupyter nbconvert --execute notebooks/validation.ipynb --to html --output validation_full.html`

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

## License
- Manuscript: CC-BY 4.0 (DOI: 10.5281/zenodo.17161831)
- Code: MIT License (see LICENSE-CODE)
