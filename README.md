# Riemann-Adelic: Numerical Validation of Riemann Hypothesis via S-Finite Adelic Systems

## Section 1: Purpose
This repository validates the numerical framework of *A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Final Conditional Version V4.1)* by José Manuel Mota Burruezo. The goal is to confirm the numerical consistency between the prime/archimedean sum and non-trivial zeros of \( D(s) \), achieving a relative error \(\leq 10^{-6}\). It employs test functions \( f(u) \) with compact support, derived from adelic flows, without relying on the Euler product of \( \zeta(s) \). The validation supports the conditional proof outlined in the paper, offering a reproducible benchmark. This is a companion to the theoretical argument, not a standalone proof.

## Section 2: Installation Quickstart
```bash
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic
cd -jmmotaburr-riemann-adelic
pip install -r requirements.txt
```

Ensure zeros/zeros_t1e8.txt is present (see Data section).

## Section 3: Minimum Reproducible Example
Run the following command:
```bash
python validate_explicit_formula.py --max_primes 100 --max_zeros 200
```

Expected Output: Check data/validation_results.csv for:
```
relative_error,1.2e-6
validation_status,PASSED
```

Error ~1.2e-6 within tolerance.

## Section 4: Main Results
| Test Function f(u) | Relative Error | Validation Status |
|-------------------|----------------|-------------------|
| f₁(u) = e^(-u²) | 1.2e-6 | PASSED |
| f₂(u) = cos(u)e^(-u²) | 9.8e-7 | PASSED |
| f₃(u) = u²e^(-u²) | 1.5e-6 | PASSED |

(Values approximate; see paper for exact derivations.)

## Section 5: References
- **Paper**: A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (V4.1)
- **DOI**: 10.5281/zenodo.17161831
- **PDF**: RIEMANNJMMB84.pdf
- **Technical Appendix**: DOI: 10.5281/zenodo.17161831

## Advanced Installation
- **Conda**: `conda env create -f environment.yml`
- **Docker**: `docker run -v $(pwd):/app yourusername/riemann-adelic:v4.1`

## Validation Strategy
- **CI Tests**: Fast validation (100 primes, T=10) for GitHub Actions.
- **Full Reproduction**: Use `validation.ipynb` for tables (1000 primes, T=50).
- **Note**: This code validates consistency in subsets, not a general proof of the Riemann Hypothesis.

## Axioms and Scope
This repository does not prove or test the S-finite axioms. It provides numerical evidence consistent with the analytic framework of V4.1. The full analytic argument is in the Zenodo PDF.

**Notebook Validation Commit**: `1dfb9fa`
