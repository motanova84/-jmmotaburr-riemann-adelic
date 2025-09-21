# Zero Data Documentation

This directory contains precomputed zeros of the Riemann zeta function, sourced from Andrew Odlyzko's extensive computational tables.

## Data Source

- **Origin**: Odlyzko zero data, height up to \(10^8\), latest release
- **Source**: [https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1.gz](https://www-users.cse.umn.edu/~odlyzko/zeta_tables/zeros1.gz)
- **License**: Public Domain (common academic use, cite Odlyzko)
- **Validation**: Checksum (MD5) computed via `utils/checksum_zeros.py`
- **Note**: Contains ~100,000 zeros; full dataset available at source link

## About Odlyzko's Tables

Andrew Odlyzko, a mathematician known for his work in number theory and computation of zeros of the Riemann zeta function, has published extensive tables of non-trivial zeros. These tables are widely used by researchers to validate hypotheses and perform numerical calculations.

### Key Features:

- **High Precision**: Generally >1000 decimals for the first zeros
- **Extensive Range**: Tables cover zeros up to heights of \(10^{22}\)
- **Validated**: Computed using fast evaluation algorithms for the zeta function
- **Widely Used**: Standard reference in the mathematical community

## File Format

Each file contains one zero per line, representing the imaginary parts of non-trivial zeros:
```
14.134725142
21.022039639
25.010857580
...
```

## Files in this Directory

- `zeros_t1e8.txt` - First ~100,000 zeros up to height \(10^8\)
- `zeros_t1e8.txt.gz` - Compressed version of the above

## Usage

The zeros data is used by the validation scripts in this repository:

- `validate_explicit_formula.py` - Main validation script
- `validate_by_height.py` - Height-specific validation
- `validation.ipynb` - Jupyter notebook for interactive validation

## Data Integrity

To verify the integrity of downloaded data:

```bash
python utils/checksum_zeros.py zeros/zeros_t1e8.txt
```

## Downloading Fresh Data

To download the latest data from Odlyzko's website:

```bash
python utils/fetch_odlyzko.py
```

This script will:
1. Check if data already exists locally
2. Download from the official source if needed
3. Validate the format
4. Extract and place in the correct location

## Scalability

For research requiring more zeros (e.g., \(10^{12}\) or \(10^{22}\) range), additional files are available at Odlyzko's website. The fetch script can be modified to download these larger datasets:

- `zeros12.gz` - Zeros in the \(10^{12}\) range
- Additional files for higher ranges

## Citation

When using this data, please cite:

> Odlyzko, A. M. "Tables of zeros of the Riemann zeta function", available at https://www-users.cse.umn.edu/~odlyzko/zeta_tables/

## References

- Odlyzko, A. M. (1987, 2001), various publications in Math. Comp. and other journals
- Documentation: https://www-users.cse.umn.edu/~odlyzko/doc/zeta.tables/
- SageMath integration: https://doc.sagemath.org/html/en/reference/arithgroup/sage/databases/numtheory.html#database-odlyzko-zeta