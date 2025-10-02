# Verification Scripts

This directory contains numerical verification scripts for the V5.2 adelic proof framework.

## 🆕 New V5.2 Scripts

### `verify_a4_commutativity.py`

**Purpose**: Validates A4 formal derivation - proves ℓ_v = log q_v emerges from commutativity

**What it does**:
- Tests commutativity of local unitary operators U_v and scale flow S_u
- Derives orbit lengths from geometric constraints (no prior assumption)
- Verifies Haar measure invariance on adelic group GL₁(𝔸_ℚ)
- Confirms no circular dependency on ζ(s) or Ξ(s)

**Usage**:
```bash
python3 scripts/verify_a4_commutativity.py --precision 40
```

**Output**:
- ✅ All tests passed: Commutativity confirmed, ℓ_v = log q_v derived
- Test results for primes p=2,3,5,7,11,...

**Reference**: Corresponds to `formalization/lean/RiemannAdelic/lengths_derived.lean`

---

### `validate_explicit_formula_extended.py`

**Purpose**: S → ∞ convergence validation for explicit formula

**What it does**:
- Tests explicit formula balance as finite set S grows
- Validates zero stability on critical line Re(s) = 1/2
- Verifies pole at s=1 is correctly handled
- Stress tests with high precision (up to 100 decimal places)

**Usage**:
```bash
python3 scripts/validate_explicit_formula_extended.py \
  --precision 40 \
  --max-zeros 1000 \
  --max-primes 1000
```

**Output**:
- Convergence data for increasing S sizes
- Zero stability metrics
- Pole handling validation

**Reference**: Addresses "Extensión de S-Finito a Infinito" requirement

---

## Existing Scripts

### `verify_status.py`

Status verification and reporting for the overall project.

---

## Requirements

All scripts require:
- Python 3.8+
- mpmath >= 1.3.0
- numpy >= 1.22.4
- sympy >= 1.12 (for some scripts)

Install dependencies:
```bash
pip install -r requirements.txt
```

---

## Integration with Lean Formalization

These Python scripts provide **numerical verification** to complement the **formal proofs** in Lean 4:

| Lean Module | Python Verification |
|-------------|---------------------|
| `lengths_derived.lean` | `verify_a4_commutativity.py` |
| `uniqueness_without_xi.lean` | (theoretical - no numerical analog) |
| Explicit formula convergence | `validate_explicit_formula_extended.py` |

---

## Running All Verifications

To run all V5.2 verification tests:

```bash
# A4 commutativity test
python3 scripts/verify_a4_commutativity.py --precision 30

# Extended validation (S → ∞)
python3 scripts/validate_explicit_formula_extended.py \
  --precision 30 \
  --max-zeros 100 \
  --max-primes 100

# Main V5 coronación validation
python3 validate_v5_coronacion.py --precision 30 --verbose
```

---

## Expected Results

### A4 Commutativity (Success)
```
🎉 A4 VERIFICATION: ALL TESTS PASSED
✅ Commutativity confirmed
✅ Orbit lengths ℓ_v = log q_v derived
✅ Haar invariance verified
✅ No circular dependency on ζ(s) or Ξ(s)
```

### Extended Validation (Partial - as expected for simplified model)
```
✅ Zero stability on critical line confirmed
⚠️  Explicit formula balance needs full implementation
✅ Foundation for S→∞ convergence established
```

---

## Theory References

- **Tate (1967)**: "Fourier analysis in number fields and Hecke's zeta-functions"
- **Birman-Solomyak (1977)**: "Spectral theory of self-adjoint operators"
- **Simon (2005)**: "Trace ideals and their applications"
- **Levin (1956)**: "Distribution of zeros of entire functions"
- **Paley & Wiener (1934)**: "Fourier transforms in the complex domain"

---

## Contributing

When adding new verification scripts:
1. Include docstrings with theory references
2. Make scripts executable: `chmod +x script_name.py`
3. Add argparse for command-line flexibility
4. Include verbose output mode
5. Return exit code 0 on success, 1 on failure
6. Update this README

---

## Contact

For questions about verification scripts or numerical methods:
- See main repository README
- Reference Lean formalization in `formalization/lean/`
