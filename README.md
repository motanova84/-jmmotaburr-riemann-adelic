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

## 🚀 Enhanced Computational Validation

**New in V4**: This repository now features a comprehensive computational validation framework with:

- **SHA256 Integrity Verification**: Every result is cryptographically verifiable
- **CSV Data Export**: Structured outputs for reproducible analysis
- **Partial Simulation Runs**: Fast validation for development and testing
- **Automated Analysis Tools**: Statistical comparison and error analysis
- **Continuous Integration**: Automated validation on every code change

### Quick Start

```bash
# Fast development validation
python validate_enhanced.py --partial --max-primes 100 --max-zeros 50

# Full publication-quality validation  
python validate_enhanced.py --full --max-primes 10000 --max-zeros 2000

# Analyze and verify results
python analyze_results.py --directory data/validation_runs --verify --analyze
```

See [Computational Validation Documentation](docs/COMPUTATIONAL_VALIDATION.md) for complete details.

## 📂 Structure

```plaintext
.
├── docs/
│   └── COMPUTATIONAL_VALIDATION.md    # Enhanced validation framework docs
├── notebooks/                         # Jupyter notebooks (e.g. validation.ipynb)
├── utils/
│   ├── mellin.py                      # Tools for computing Mellin transforms
│   ├── validation_core.py             # 🆕 Core validation engine with integrity
│   └── riemann_tools.py               # Riemann-specific computational tools
├── zeros/
│   └── zeros_t1e8.txt                 # List of zeros at height t ~ 1e8 (from Odlyzko)
├── data/
│   └── validation_runs/               # 🆕 Archived validation results (CSV/JSON)
├── validate_explicit_formula.py       # Original CLI validation script
├── validate_enhanced.py               # 🆕 Enhanced CLI with integrity verification
├── analyze_results.py                 # 🆕 Analysis and verification tools
├── validate_by_height.py             # Height-specific validation
├── requirements.txt
└── README.md
```

## 🔒 Data Integrity & Reproducibility

The enhanced framework ensures:

- **Bit-identical Results**: SHA256 verification of computational outcomes
- **Parameter Tracking**: Complete documentation of all input parameters  
- **Error Analysis**: Statistical bounds on numerical accuracy
- **Version Control**: Timestamped validation runs with full provenance

## 🤖 Automated Validation

GitHub Actions automatically:
- Runs validation on every code push
- Verifies result integrity
- Archives computational data
- Generates comparison reports

Manual validation triggers support configurable parameters for custom validation scenarios.

## 🧠 Copilot Integration

This repository is optimized for AI-assisted development. Use this comprehensive prompt:

```
🧠 Enhanced Copilot Prompt: 
Suggest workflows for the computational validation framework:
- Running enhanced validation with validate_enhanced.py
- Analyzing results with SHA256 integrity verification
- Generating CSV outputs for statistical analysis
- Setting up automated validation pipelines
- Comparing validation runs across different parameters
- Implementing new test functions and mathematical checks
- Debugging numerical accuracy issues
- Creating reproducible research outputs
```

## 📊 Results & Verification

All validation results include:
- **Computational Values**: Prime sums, Archimedean contributions, zero sums
- **Error Bounds**: Absolute and relative error analysis
- **Integrity Hashes**: SHA256 verification for data authenticity
- **Metadata**: Complete parameter sets and timestamps

Results are saved in both human-readable CSV and machine-readable JSON formats for maximum accessibility and interoperability.
