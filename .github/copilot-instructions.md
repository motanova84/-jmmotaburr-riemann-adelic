# 🤖 GitHub Copilot Instructions for -jmmotaburr-riemann-adelic

## Core Principles

### 1. Mathematical Accuracy and Reproducibility
- **Always prioritize mathematical accuracy and reproducibility** in all code contributions
- Execute or suggest validation scripts (particularly `validate_v5_coronacion.py`) before generating new code
- Maintain consistency with existing mathematical frameworks and proof structures
- Ensure numerical stability and precision in all calculations

### 2. Validation Before Code Generation
- **Run validation scripts before proposing changes**:
  ```bash
  python3 validate_v5_coronacion.py --precision 30
  python3 validar_v5_coronacion.py
  ```
- Verify that existing tests pass: `pytest tests/ -v`
- Check for mathematical consistency with QCAL-CLOUD framework

### 3. Protected References
**Never remove or modify references to:**
- Zenodo DOI: `10.5281/zenodo.17116291`
- Lean4 formalization code in `formalization/lean/`
- QCAL-CLOUD infrastructure and beacon files (`.qcal_beacon`)
- Existing proof structures and mathematical foundations

## Code Quality Standards

### 4. Performance Optimization
Suggest performance improvements when detecting intensive loops or computations:
- **Numba**: For JIT compilation of numerical loops
- **JAX**: For automatic differentiation and GPU/TPU acceleration
- **CuPy**: For GPU-accelerated array operations
- **Numexpr**: For fast evaluation of complex expressions

Example suggestion format:
```python
# Consider using Numba for this intensive loop:
@numba.jit(nopython=True)
def compute_spectral_trace(matrix, n_iterations):
    # ... implementation
```

### 5. Documentation Standards
**Automatically add to all Python functions:**
- Comprehensive docstrings (Google or NumPy style)
- Type annotations for parameters and return values
- Mathematical context when relevant

Example:
```python
def compute_adelic_trace(s: complex, precision: int = 30) -> complex:
    """
    Compute the adelic trace at complex point s.
    
    Args:
        s: Complex point on the critical line (typically Re(s) = 1/2)
        precision: Decimal precision for mpmath calculations
        
    Returns:
        Complex trace value D(s) via S-finite adelic flows
        
    References:
        - Burruezo, J.M. (2025). DOI: 10.5281/zenodo.17116291
        - Section 3.2: Adelic Spectral Systems
    """
    # ... implementation
```

### 6. Module Integration
When creating a new module:
- **Always link it in `IMPLEMENTATION_SUMMARY.md`**
- Add appropriate tests in `tests/`
- Update relevant README files
- Add entry to the repository structure documentation

## API and External Services

### 7. External API Usage
- **Do not use external APIs without explicit confirmation**
- Always ask before:
  - Making network requests
  - Downloading external data (except approved sources like Odlyzko zeros)
  - Using third-party web services
  - Accessing external databases

Approved data sources:
- Odlyzko Riemann zeros: `https://www-users.cse.umn.edu/~odlyzko/zeta_tables/`
- Zenodo repository: `https://doi.org/10.5281/zenodo.17116291`

## Pull Request Guidelines

### 8. Success Message Template
When closing a successful PR, **always comment**:

```
✅ Validación completada. Coherencia QCAL confirmada.

**Validation Results:**
- Mathematical accuracy: ✅ Verified
- All tests passing: ✅ Confirmed
- Reproducibility: ✅ Validated
- QCAL-CLOUD coherence: ✅ Maintained

**Verification Commands:**
\`\`\`bash
python3 validate_v5_coronacion.py --precision 30
pytest tests/ -v
\`\`\`
```

### 9. Code Review Checklist
Before submitting changes, verify:
- [ ] Mathematical correctness validated
- [ ] Validation scripts executed successfully
- [ ] All tests pass (`pytest tests/ -v`)
- [ ] Type annotations added
- [ ] Docstrings comprehensive
- [ ] No removal of DOI/Lean4/QCAL references
- [ ] Performance optimizations suggested where applicable
- [ ] New modules linked in `IMPLEMENTATION_SUMMARY.md`
- [ ] No unauthorized external API calls

## Repository-Specific Guidelines

### 10. Mathematical Framework
- Respect the S-finite adelic spectral system approach
- Maintain the non-circular construction: `A₀ → H → D(s) ≡ Ξ(s)`
- Preserve the geometric-first paradigm (not prime-dependent)
- Keep quantum vacuum energy equations intact

### 11. Validation Hierarchy
Priority order for validation:
1. `validate_v5_coronacion.py` - V5 Coronación complete validation
2. `validate_critical_line.py` - Critical line verification
3. `validate_explicit_formula.py` - Weil explicit formula
4. Unit tests in `tests/` directory
5. Notebook validation: `notebooks/validation.ipynb`

### 12. Language and Documentation
- Primary documentation language: Spanish (es)
- Code comments: English or Spanish
- Mathematical notation: Standard LaTeX
- Always maintain bilingual README sections where they exist

## Special Considerations

### 13. Formalization (Lean4)
When working with Lean4 code:
- Maintain skeleton structure with `axiom` and `sorry`
- Don't claim proofs are complete unless verified
- Link to mathematical paper sections
- Update `FORMALIZATION_STATUS.md` when changing Lean files

### 14. Continuous Integration
- Ensure changes pass all CI/CD workflows
- Monitor GitHub Actions for validation results
- Check codecov reports for test coverage
- Verify that new code doesn't break existing workflows

### 15. Security and Integrity
- Never commit secrets or API keys
- Maintain `.qcal_beacon` file integrity
- Preserve hash and frequency metadata in schema files
- Don't modify universal kernel validation logic without review

## Quick Reference Commands

```bash
# Full validation suite
python3 validate_v5_coronacion.py --precision 30 --verbose

# Run all tests
pytest tests/ -v

# Run specific test categories
pytest tests/test_genuine_contributions.py -v

# Check code coverage
pytest tests/ --cov=. --cov-report=html

# Verify Lean formalization status
cat formalization/lean/README.md

# Check QCAL coherence
python3 tools/universal_kernel.py --audit

# Performance benchmark
python3 demo_advanced_math_libraries.py
```

## Version and Updates
- **Version**: 1.0
- **Last Updated**: 2025-10-20
- **Scope**: Full repository guidance for GitHub Copilot
- **Maintained by**: @motanova84

---

**Remember**: This repository represents a historic mathematical proof. Every change must preserve the integrity of the Riemann Hypothesis demonstration while advancing reproducibility and clarity.

*"La belleza es la verdad, la verdad belleza." — John Keats*
