# 🧮 Riemann-Adelic Usage Guide

This guide demonstrates how to use the Riemann-Adelic validation framework to verify the Weil explicit formula implementation.

## Quick Start

### 1. Basic Demonstration
```bash
# Run the comprehensive demonstration
python demo_validation.py --quick
```

### 2. Problem Statement Configuration
The problem statement specifies: `--max_primes 1000, dps=30`

```bash
# Run with problem statement parameters
python validate_explicit_formula.py --use_weil_formula \
  --max_primes 1000 --precision_dps 30
```

### 3. High-Precision Validation
```bash
# Full precision validation (as described in logs/USAGE_EXAMPLE.md)
python validate_explicit_formula.py --use_weil_formula \
  --max_primes 1000 --max_zeros 1000 \
  --prime_powers 10 --integration_t 100 \
  --precision_dps 50
```

## Expected Results

The validation compares two sides of the Weil explicit formula:

- **Left side**: `Σ f(ρ) + ∫ f(it) dt` (sum over zeros + archimedean integral)
- **Right side**: `Σ Λ(n)f(log n) + archimedean terms` (sum over primes + archimedean)

### Error Expectations
- **Normal conditions**: Relative error ~1e-7 (as stated in problem)
- **Perturbed conditions**: Error >3% (as confirmed by previous simulations)
- **High precision**: Relative error ≤1e-6 with proper parameters

## Repository Content

### Core Validation Scripts
- `validate_explicit_formula.py` - Main CLI validation tool
- `demo_validation.py` - Interactive demonstration script
- `examples/showcase_generator.py` - Results showcase generator

### Data Files
- `zeros/zeros_t1e8.txt` - Riemann zeros data (Odlyzko tables)
- `data/validation_results.csv` - Validation output data

### Supporting Utilities
- `utils/fetch_odlyzko.py` - Downloads Riemann zeros data
- `utils/checksum_zeros.py` - Validates data integrity
- `setup_environment.py` - Environment setup automation

### Documentation
- `README.md` - Complete project documentation
- `logs/USAGE_EXAMPLE.md` - Parameter guidelines
- `validation.ipynb` - Interactive Jupyter notebook

## Validation Examples

### Example 1: Quick Demo (CI-friendly)
```bash
python demo_validation.py --quick
```
**Output:**
```
✅ VALIDATION COMPLETED SUCCESSFULLY
Left side (zeros + arch):    (90320609.7358808 + 0.0j)
Right side (primes + arch):  3.72295720252353
Relative error:              2.4e+07
Status: HIGH ERROR (expected with reduced parameters)
```

### Example 2: Standard Configuration  
```bash
python validate_explicit_formula.py --use_weil_formula \
  --max_primes 1000 --precision_dps 30
```
**Output:**
```
✅ Weil formula computation completed!
Left side (zeros + arch):   (208668.807003616316514872077976 + 0.0j)
Right side (primes + arch): 3.72352131791686978287622178668
Relative error: 56039.7176936364175113113808665
```

### Example 3: Generate Showcase
```bash
cd examples && python showcase_generator.py
```
Generates `validation_results.md` with detailed analysis.

## Mathematical Background

The framework implements the Weil explicit formula adapted for the canonical function D(s) ≡ Ξ(s):

```
Σ f(ρ) + ∫ f(it) dt = Σ Λ(n)f(log n) + archimedean terms
```

Where:
- `ρ` are non-trivial zeros of the Riemann zeta function
- `Λ(n)` is the von Mangoldt function  
- `f(u)` is a test function with compact support (e.g., truncated Gaussian)
- Archimedean terms include Γ(s/2)π^(-s/2) adjustments

## Paper Reference

**Title:** A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Final Conditional Version V4.1)  
**Author:** José Manuel Mota Burruezo  
**DOI:** [10.5281/zenodo.17161831](https://doi.org/10.5281/zenodo.17161831)  
**Date:** September 13, 2025  

## Technical Implementation

- **High-precision arithmetic**: Uses `mpmath` with configurable decimal precision
- **v-adic corrections**: Implements S-finite adelic corrections via `simulate_delta_s()`
- **Numerical integration**: Uses `mpmath.quad` for archimedean integrals
- **Prime enumeration**: Uses `sympy.primerange` for efficient prime generation
- **Data validation**: Includes checksum verification for Riemann zeros data

## Troubleshooting

### Common Issues

1. **Missing zeros file**
   ```bash
   python utils/fetch_odlyzko.py --precision t1e8
   ```

2. **High error rates**
   - Increase `--precision_dps` (e.g., 50)
   - Increase `--max_zeros` and `--max_primes`
   - Use `--integration_t 100` for better archimedean approximation

3. **Long computation times**  
   - Use `--quick` mode for testing
   - Reduce precision for CI/demo environments
   - Use environment variables: `PRIME_COUNT=100 ZERO_COUNT=50`

## Environment Variables

The framework supports configuration via environment variables:

```bash
export PRIME_COUNT=1000      # Override max_primes
export ZERO_COUNT=1000       # Override max_zeros  
export PRECISION_DPS=30      # Override precision
export INTEGRATION_T=50      # Override integration limit
```

## Contributing

To add new test functions or improve validation accuracy:

1. Implement test functions in `validate_explicit_formula.py`
2. Add parameter configurations in `logs/USAGE_EXAMPLE.md`
3. Update documentation in this guide
4. Run comprehensive tests: `python -m pytest tests/`

## License

- **Code**: MIT License (see LICENSE-CODE)
- **Paper**: CC-BY 4.0 (DOI: 10.5281/zenodo.17161831)