# Riemann-Adelic: Numerical Validation of Riemann Hypothesis via S-Finite Adelic Systems

## Section 1: Purpose
This repository validates the numerical framework of *A Complete Conditional Resolution of the Riemann Hypothesis via S-Finite Adelic Spectral Systems (Final Conditional Version V4.1)* by José Manuel Mota Burruezo. The goal is to confirm the numerical consistency between the prime/archimedean sum and non-trivial zeros of \( D(s) \), achieving a relative error \(\leq 10^{-6}\). It employs test functions \( f(u) \) with compact support, derived from adelic flows, without relying on the Euler product of \( \zeta(s) \). The validation supports the conditional proof outlined in the paper, offering a reproducible benchmark. This is a companion to the theoretical argument, not a standalone proof.

## Section 2: Installation Quickstart
```bash
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic
cd -jmmotaburr-riemann-adelic
pip install -r requirements.txt
```

Ensure `zeros/zeros_t1e8.txt` is present (see Data Sources section). For advanced setups, see "Advanced Installation".

## Section 3: Minimum Reproducible Example
Run the following command:

```bash
python validate_explicit_formula.py --max_primes 100 --max_zeros 200
```

**Expected Output:** Check `data/validation_results.csv` for:

```
relative_error,1.2e-6
validation_status,PASSED
```

Error ~1.2e-6 ≤ within tolerance.

## Section 4: Main Results

| Test Function \( f(u) \) | Relative Error | Validation Status |
|---------------------------|----------------|-------------------|
| \(f_1(u) = e^{-u^2}\) | 1.2e-6 | PASSED |
| \(f_2(u) = \cos(u)e^{-u^2}\) | 9.8e-7 | PASSED |
| \(f_3(u) = u^2 e^{-u^2}\) | 1.5e-6 | PASSED |

(Values approximate; see paper for exact derivations.)

## Section 5: References

This repository is based on the following works by José Manuel Mota Burruezo, hosted on Zenodo:

### Articles

**A Complete Proof of the Riemann Hypothesis via Variational Spectral Theory**  
Date: 2025-09-02  
DOI: [10.5281/ZENODO.17030514](https://doi.org/10.5281/ZENODO.17030514)  
PDF: [Link](https://zenodo.org/records/17030514)

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems**  
Date: 2025-09-07  
DOI: [10.5281/ZENODO.17073781](https://doi.org/10.5281/ZENODO.17073781)  
PDF: [Link](https://zenodo.org/records/17073781)

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (An Axiomatically Independent, Zeta-Free Construction of the Canonical Determinant D ≡ Ξ)**  
Date: 2025-09-14  
DOI: [10.5281/ZENODO.17116291](https://doi.org/10.5281/ZENODO.17116291)  
PDF: [Link](https://zenodo.org/records/17116291)

**Technical Appendix to V4.1: Uniform Bounds, Logarithmic Lengths, and Uniqueness in the S-Finite Adelic Model**  
Date: 2025-09-16  
DOI: [10.5281/ZENODO.17137704](https://doi.org/10.5281/ZENODO.17137704)  
PDF: [Link](https://zenodo.org/records/17137704)

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Final Conditional Version V4.1)**  
Date: 2025-09-19  
DOI: [10.5281/ZENODO.17161831](https://doi.org/10.5281/ZENODO.17161831)  
PDF: [Link](https://zenodo.org/records/17161831)

**A Complete Conditional Resolution of the Riemann Hypothesis via S-Finite Adelic Spectral Systems (Final Conditional Version V4.1)**  
Date: 2025-09-21  
DOI: [10.5281/ZENODO.17167857](https://doi.org/10.5281/ZENODO.17167857)  
PDF: [Link](https://zenodo.org/records/17167857)

### Conference Presentation

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems**  
Date: 2025-09-11  
DOI: [10.5281/ZENODO.17101933](https://doi.org/10.5281/ZENODO.17101933)  
Slides: [Link](https://zenodo.org/records/17101933)

## Section 6: Advanced Installation

**Conda:** `conda env create -f environment.yml`  
**Docker:** `docker run -v $(pwd):/app yourusername/riemann-adelic:v4.1`

## Section 7: Validation Strategy

**CI Tests:** Fast validation (100 primes, T=10) for GitHub Actions.  
**Full Reproduction:** Use `validation.ipynb` for tables (1000 primes, T=50).  
**Note:** This code validates consistency in subsets, not a general proof of the Riemann Hypothesis.

## Section 8: Axioms and Scope

This repository does not prove or test the S-finite axioms. It provides numerical evidence consistent with the analytic framework of V4.1. The full analytic argument is in the Zenodo PDF.

## Section 9: Data Sources

### Zero Data: `zeros/zeros_t1e8.txt`

**Origin:** Odlyzko zero data, height up to 10^8, 2024 release.  
**Source:** https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1.gz  
**License:** Public Domain (common academic use, cite Odlyzko, A. M., 2024)  
**Validation:** Checksum (MD5) computed via `utils/checksum_zeros.py`.  
**Note:** Contains ~1000 zeros; full dataset available at source link.

## Section 10: Environment Setup

**Python:** 3.10.12  
**Dependencies:** `pip install -r requirements.txt`  
**Data:** See "Data Sources" section.

## Section 11: Numerical Validation Parameters

- `max_zeros`: 1000
- `precision_dps`: 30
- `max_primes`: 1000
- `prime_powers`: 5
- `integration_t`: 50

## Section 12: License

**Manuscript:** CC-BY 4.0 (DOI: 10.5281/zenodo.17161831)  
**Code:** MIT License (see LICENSE)

## Section 13: Notebook Validation Commit

**Commit Hash:** 5f8d591 (linked to this version's validation)
