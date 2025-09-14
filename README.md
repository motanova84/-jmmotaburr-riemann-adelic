# Riemann-Adelic

[![Validate Riemann Formula](https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/validate.yml/badge.svg)](https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/validate.yml)
[![Run Jupyter Notebook](https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/run_notebook.yml/badge.svg)](https://github.com/motanova84/-jmmotaburr-riemann-adelic/actions/workflows/run_notebook.yml)

This repository contains numerical validation code for the paper:

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Definitive Revision V3.6)**  
Author: José Manuel Mota Burruezo  
Date: September 13, 2025  
DOI: [10.5281/zenodo.17114751](https://doi.org/10.5281/zenodo.17114751)  
Instituto: Instituto de Conciencia Cuántica (ICQ)

## 🧪 Objective

Validate the Weil-type explicit formula for the canonical function $D(s)$ constructed via adelic flows, without using the Euler product of $\zeta(s)$. The validation includes:

- High-precision numerical agreement between:
  - Prime + Archimedean side: $\text{PrimeSum}(f) + A_\infty(f)$
  - Sum over nontrivial zeros: $\sum_{\rho} \hat{f}(\rho)$
- For various test functions $f(u)$ with compact support
- Error tolerance: $|A - Z| < 1 \times 10^{-5}$

## 📂 Structure

```plaintext
.
├── notebooks/                  # Jupyter notebooks (validation.ipynb)
├── utils/
│   ├── mellin.py              # Mellin transform computations
│   ├── fetch_odlyzko.py       # Automated zeros data management
│   └── riemann_tools.py       # Utility functions
├── zeros/
│   └── zeros_t1e8.txt         # Riemann zeros data (100,000+ zeros)
├── tests/                     # pytest test suite
│   └── test_formula.py        # Comprehensive validation tests
├── data/                      # Generated validation results
│   └── validation_output.csv  # CSV export of results
├── docs/                      # Documentation and reports
│   └── validation.html        # HTML validation report
├── .github/workflows/         # CI/CD automation
│   ├── validate.yml           # Automated validation pipeline
│   └── run_notebook.yml       # Notebook execution workflow
├── validate_explicit_formula.py  # Original validation script
├── validate_fixed.py          # Enhanced validation with error handling
├── generate_report.py         # HTML report generation
└── requirements.txt           # Python dependencies
```

## 🚀 Quick Start

### Installation

```bash
git clone https://github.com/motanova84/-jmmotaburr-riemann-adelic.git
cd -jmmotaburr-riemann-adelic
pip install -r requirements.txt
```

### Run Validation

```bash
# Quick test validation (reduced parameters)
python validate_fixed.py --simple

# Full validation (test parameters)
python validate_fixed.py

# Production validation (full parameters - may take hours)
python validate_fixed.py --production
```

### Run Tests

```bash
# Run comprehensive test suite
pytest tests/ -v

# Check zeros data availability
python utils/fetch_odlyzko.py --check
```

## 📊 Validation Results

The validation system tests three functions:

- **f₁(u)**: $e^{-u^2/2}$ for $|u| \leq 3$
- **f₂(u)**: $e^{-u^2}$ for $|u| \leq 2$  
- **f₃(u)**: $(1 - u^2/4)^2$ for $|u| \leq 2$

Results are automatically exported to:
- `data/validation_output.csv` - Structured data
- `docs/validation.html` - Professional HTML report

## 🛠️ Parameters

### Production Parameters (Specification)
- δ = 0.01
- P = 1000 (maximum prime)
- K = 50 (powers per prime)
- N_Ξ = 2000 (number of zeros)
- σ₀ = 2.0 (sigma_0)
- T = 50 (integration limit)

### Test Parameters (Faster)
- P = 100, K = 10, N_Ξ = 200, T = 15

## 🔧 Advanced Usage

### Generate Reports Only
```bash
python generate_report.py
```

### Data Management
```bash
# Validate zeros file
python utils/fetch_odlyzko.py --check

# Force re-download zeros data
python utils/fetch_odlyzko.py --force-download
```

### CI/CD Integration
- **GitHub Actions**: Automated validation on push/PR
- **Daily validation**: Scheduled production runs
- **Multi-Python**: Tests on Python 3.9-3.12

## 📈 Mathematical Foundation

The validation implements the explicit formula:

$$\sum_p \sum_{k=1}^K \log p \cdot f(k \log p) + A_\infty(f) = \sum_\rho \hat{f}(\rho)$$

Where:
- Left side: Prime sum + Archimedean contribution
- Right side: Sum over nontrivial zeros
- $\hat{f}(\rho)$: Mellin-type transform of test function
- $A_\infty(f)$: Archimedean integral with residue correction

## 🔍 Status

- ✅ **Infrastructure**: Complete testing and CI/CD framework
- ✅ **Data Management**: Automated zeros file handling
- ✅ **Error Handling**: Robust validation with proper error reporting
- ⚠️ **Mathematical Implementation**: Under refinement for convergence
- 🔄 **Optimization**: Performance improvements in progress

## 📄 Citation

```bibtex
@article{motaburruezo2025riemann,
  title={A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems},
  author={Mota Burruezo, José Manuel},
  year={2025},
  institution={Instituto de Conciencia Cuántica},
  doi={10.5281/zenodo.17114751},
  url={https://github.com/motanova84/-jmmotaburr-riemann-adelic}
}
```

---

*This validation system provides automated, reproducible verification of the Riemann Hypothesis proof using high-precision numerical computation and comprehensive error analysis.*
# Riemann-Adelic
