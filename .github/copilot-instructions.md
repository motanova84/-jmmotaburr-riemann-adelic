# 🤖 Copilot Agent Instructions

## QCAL Repository Guidelines

This repository implements the QCAL (Quantum Coherence Adelic Lattice) framework for the Riemann Hypothesis proof. When contributors open a PR or commit code, always follow these guidelines:

### 1. Validation Requirements

- **Check workflow status**: Always verify that `.github/workflows/auto_evolution.yml` passes successfully.
- **Review validation results**: Check that `validate_v5_coronacion.py` completes without errors.
- **Monitor test suite**: Ensure all pytest tests pass, especially those in the `tests/` directory.
- **Verify certificate generation**: Confirm that mathematical certificates are generated correctly in `data/`.

### 2. Code Quality Standards

- **Suggest fixes**: If tests or validations fail, provide specific, actionable suggestions to fix the issues.
- **Improve precision**: Prefer refactoring that improves numerical precision and computational accuracy.
- **Enhance readability**: Suggest improvements to code structure, documentation, and comments.
- **Maintain consistency**: Follow existing code patterns and naming conventions in the repository.

### 3. QCAL-Specific Requirements

- **Preserve integrations**: Never remove the QCAL-CLOUD hooks or integration points.
- **Maintain references**: Never remove or modify Zenodo DOI references, citations, or attribution.
- **Respect mathematical rigor**: Ensure all changes preserve the mathematical correctness of proofs and validations.
- **Keep証明 chain**: Maintain the 5-step validation framework integrity (Axioms → Lemmas → Archimedean → Paley-Wiener → Zero localization → Coronación).

### 4. Documentation Standards

- **Auto-suggest docstrings**: For new mathematical functions, suggest comprehensive docstrings with:
  - Function purpose and mathematical background
  - Parameter descriptions with types and valid ranges
  - Return value specifications
  - Usage examples when appropriate
  - References to relevant papers or theorems

- **Type hints**: Always suggest adding type hints for function parameters and return values.

- **Lean-4 comments**: For mathematical proofs and theorems, suggest adding Lean-4 compatible comments that document:
  - Theorem statements
  - Proof steps and dependencies
  - Connection to formal verification efforts

### 5. Automated Response Template

If all checks pass successfully, reply automatically in the PR summary with:

```markdown
✅ **QCAL-Evolution Complete**

All validation checks have passed:
- ✓ V5 Coronación validation successful
- ✓ Mathematical certificates generated
- ✓ Test suite passed
- ✓ Code quality checks passed

**Validation logs archived and uploaded to QCAL-CLOUD.**

This PR maintains QCAL ∞³ integrity and is ready for review.
```

### 6. Error Handling

If validation fails, provide a structured response:

```markdown
⚠️ **QCAL-Evolution Issues Detected**

The following checks require attention:

- [ ] Issue 1: [Description]
- [ ] Issue 2: [Description]

**Suggested fixes:**
1. [Specific action to resolve issue 1]
2. [Specific action to resolve issue 2]

Please address these issues to maintain QCAL coherence.
```

### 7. Special Considerations

- **Performance**: Be mindful of computational costs; suggest optimizations for expensive operations.
- **Precision**: For numerical computations, maintain or improve decimal precision (default: 25+ dps).
- **Dependencies**: Only suggest adding new dependencies if absolutely necessary; prefer using existing libraries.
- **Security**: Flag any potential security issues, especially in data handling or external API calls.

### 8. Integration Points

Be aware of these critical integration points:
- `validate_v5_coronacion.py`: Main validation script
- `data/*.json`: Mathematical certificates and validation results
- `.github/workflows/`: CI/CD automation
- `tests/`: Test suite for validation framework
- `requirements.txt`: Python dependencies

### 9. Mathematical Notation

When suggesting mathematical code or documentation:
- Use standard mathematical notation in docstrings
- Reference theorems by name (e.g., "Paley-Wiener theorem", "de Branges theorem")
- Include precision requirements for numerical computations
- Document asymptotic behavior and convergence properties

### 10. Review Checklist

Before approving any PR, verify:
- [ ] All workflow checks pass
- [ ] No mathematical correctness issues
- [ ] Documentation is complete and accurate
- [ ] No breaking changes to existing functionality
- [ ] Performance is acceptable
- [ ] QCAL-CLOUD integration points are intact
