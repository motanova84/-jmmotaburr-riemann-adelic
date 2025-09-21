# Zero Data Documentation

## Overview
This directory contains Riemann zeta function zeros data used for numerical validation of the explicit formula.

## Data Sources
- **Origin**: Odlyzko zero data, height up to 10^8, 2024 release
- **Source**: [https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1.gz](https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1.gz)
- **License**: Public Domain (common academic use, cite Odlyzko, A. M., 2024)
- **Format**: One imaginary part per line (γₙ values where ζ(½ + iγₙ) = 0)

## Files
- `zeros_t1e8.txt` - Contains ~100,000 zeros with height up to 10^8
- `zeros_t1e8.txt.gz` - Compressed version of the zeros file

## Data Validation Techniques

The repository includes comprehensive validation techniques to ensure data integrity:

### 1. Checksum Validation
- **Script**: `utils/checksum_zeros.py`
- **Purpose**: Verifies file integrity using MD5 and SHA256 checksums
- **Usage**: Compares computed checksums with known values from Odlyzko source
- **Detection**: Corruption during download or storage

### 2. Monotonicity Validation  
- **Script**: `utils/validate_monotonicity.py`
- **Purpose**: Ensures zeros are strictly increasing (fundamental property)
- **Checks**: 
  - Strict monotonicity: γₙ < γₙ₊₁
  - No duplicates
  - Gap statistics between consecutive zeros
- **Detection**: Sorting errors, duplicates, or data corruption

### 3. Known Zeros Validation
- **Script**: `utils/validate_known_zeros.py`
- **Purpose**: Validates first 10 zeros against high-precision reference values
- **Reference**: Literature values with >40 decimal precision
- **Tolerance**: 1e-9 (adjustable based on file precision)
- **Detection**: Systematic errors in computation or data corruption

### 4. Cross-validation with SageMath
- **Script**: `utils/cross_validate_zeros.py`  
- **Purpose**: Independent verification using SageMath's zeta function
- **Requirement**: SageMath installation (`pip install sagemath`)
- **Limitation**: Validates only first few zeros (SageMath less efficient for high zeros)
- **Detection**: Algorithmic errors or precision issues

## Running Validations

### Individual validation scripts:
```bash
python utils/checksum_zeros.py
python utils/validate_monotonicity.py  
python utils/validate_known_zeros.py
python utils/cross_validate_zeros.py
```

### All validations (via CI):
The GitHub Actions workflow automatically runs all validation techniques on every push.

## Data Statistics

Based on current `zeros_t1e8.txt`:
- **Count**: ~100,000 zeros
- **Range**: γ₁ ≈ 14.13 to γ₁₀₀,₀₀₀ ≈ 74,920
- **Precision**: ~12 decimal places  
- **Gap range**: 0.015 to 6.9 (between consecutive zeros)
- **Average gap**: ~0.75

## Notes

- The data contains only the imaginary parts (γₙ) of the non-trivial zeros ρₙ = ½ + iγₙ
- All zeros satisfy the Riemann-von Mangoldt asymptotic counting formula
- For full dataset or higher precision, visit the original Odlyzko source
- Validation techniques help ensure mathematical computations use reliable data

## Citations

When using this data, please cite:
- Odlyzko, A. M. (2024). Tables of zeros of the Riemann zeta function. University of Minnesota.
- This repository: Mota Burruezo, J. M. (2025). Riemann-Adelic numerical validation.