# Weil Explicit Formula Usage Examples

## Basic Usage

```bash
# Run with default parameters (original formula)
python validate_explicit_formula.py --max_primes 1000 --max_zeros 1000

# Run with Weil explicit formula 
python validate_explicit_formula.py --use_weil_formula \
  --max_primes 1000 --max_zeros 1000 \
  --precision_dps 30 --integration_t 50
```

## High-Precision Validation

For achieving the target error threshold (≤ 1e-6), use:

```bash
python validate_explicit_formula.py --use_weil_formula \
  --max_primes 10000 \
  --max_zeros 10000 \
  --prime_powers 10 \
  --integration_t 100 \
  --precision_dps 50
```

**Note:** Higher precision requires:
- More Odlyzko zeros (full `zeros_t1e8.txt` dataset)
- Higher precision arithmetic (`--precision_dps 50+`)
- More integration points (`--integration_t 100+`)
- More prime powers (`--prime_powers 10+`)

## CI/Development Testing

The CI uses reduced parameters for speed:

```bash
# CI parameters (fast but lower precision)
PRIME_COUNT=100 ZERO_COUNT=50 PRIME_POWERS=5 INTEGRATION_T=20 PRECISION_DPS=15
python validate_explicit_formula.py --use_weil_formula \
  --max_primes $PRIME_COUNT --max_zeros $ZERO_COUNT \
  --prime_powers $PRIME_POWERS --integration_t $INTEGRATION_T \
  --precision_dps $PRECISION_DPS
```

## Expected Results

- **Demo/CI**: Relative error ~0.1-1.0 (expected with limited data)
- **Full precision**: Relative error ≤ 1e-6 (requires complete dataset and high precision)