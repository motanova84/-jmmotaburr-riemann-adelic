copilot/add-production-cycle-workflow
# GitHub Copilot Instructions for QCAL Production Workflows

This document contains instructions for GitHub Copilot to automatically maintain and optimize CI/CD workflows in this repository.

## 🔄 Workflow Maintenance Rules

### 1. Detect Changes to Validation Scripts

When any `validate_*` scripts are modified (e.g., `validate_v5_coronacion.py`, `validate_critical_line.py`, etc.):

- **Suggest updates** to the production workflow (`.github/workflows/production-qcal.yml`)
- **Suggest updates** to the CI workflow (`.github/workflows/ci.yml`) if the changes affect testing
- **Verify compatibility** with Python 3.11 and ensure all new dependencies are added to `requirements.txt`
- **Check for GPU requirements** and suggest GPU runner configurations if needed

Example trigger:
```python
# If validate_v5_coronacion.py adds a new --max-zeros parameter
# Suggest adding it to production-qcal.yml workflow inputs
```

### 2. Automatically Generate New Workflows

When repetitive tasks are identified in scripts or documentation:

- **Generate new `.yml` files** in `.github/workflows` directory
- **Use descriptive names** following the pattern: `[task-name]-[frequency].yml`
- **Include appropriate triggers**: schedule, workflow_dispatch, push, pull_request
- **Add concurrency controls** to prevent duplicate runs when appropriate

Examples of tasks that warrant new workflows:
- Periodic performance benchmarking
- Nightly comprehensive validation
- Weekly dataset synchronization
- Monthly security audits

### 3. Environment Variables and Secrets Management

When code references new environment variables or API tokens:

- **Identify missing secrets** and suggest adding them to repository settings
- **Document required secrets** in workflow comments and README
- **Suggest secure alternatives** if credentials are hardcoded
- **Add validation steps** to check for required secrets before use

Required secrets for production workflows:
- `HF_TOKEN` - HuggingFace API token for dataset publishing
- `DOCKERHUB_TOKEN` - Docker Hub authentication token
- `DOCKERHUB_USERNAME` - Docker Hub username

Example suggestion:
```yaml
# ⚠️ Missing secret: HF_TOKEN
# Add in: Settings > Secrets and variables > Actions > New repository secret
# Purpose: Authenticate HuggingFace CLI for dataset uploads
```

### 4. Optimization Suggestions

Continuously analyze workflows and suggest optimizations:

#### Parallel Execution with Matrix Strategy

When multiple similar jobs exist:
```yaml
strategy:
  matrix:
    python-version: ['3.10', '3.11', '3.12']
    precision: [20, 30, 50]
  fail-fast: false
```

#### GPU Acceleration

When computational workload is detected:
- Suggest using GPU-enabled runners for mathematical computations
- Add GPU-specific dependencies (CUDA, cuDNN) when appropriate
- Configure matrix strategy to test both CPU and GPU paths

```yaml
runs-on: ${{ matrix.runner }}
strategy:
  matrix:
    runner: [ubuntu-latest, ubuntu-gpu]  # If GPU runners available
```

#### Caching Strategies

Suggest caching for:
- Python dependencies: `actions/setup-python` with `cache: 'pip'`
- Build artifacts: `actions/cache` for intermediate results
- Docker layers: `docker/build-push-action` with layer caching

#### Conditional Execution

Optimize workflow runtime by:
- Skip expensive jobs on documentation-only changes
- Use `paths` filters to trigger only relevant workflows
- Add `if` conditions to skip steps when secrets are missing

```yaml
on:
  push:
    paths-ignore:
      - '**.md'
      - 'docs/**'
```

## 🚀 Performance Best Practices

### Job Dependencies

Optimize job ordering:
- Run fast linting/validation jobs first
- Use `needs` to create dependency chains
- Run independent jobs in parallel

### Resource Management

Monitor and suggest:
- Appropriate timeout values for long-running jobs
- Resource limits for container-based workflows
- Cleanup steps for temporary files and caches

### Artifact Management

Best practices for artifacts:
- Set appropriate retention days (90 for production, 7 for CI)
- Compress large result sets before upload
- Use descriptive names with run numbers or timestamps

## 🔍 Continuous Monitoring

### Failure Detection

When workflow failures are detected:
- Analyze failure patterns across multiple runs
- Suggest adding retry logic for flaky steps
- Recommend timeout adjustments for slow operations
- Propose better error handling and logging

### Dependency Updates

Monitor `requirements.txt` changes:
- Suggest workflow updates when new packages require system dependencies
- Flag breaking changes in major version updates
- Recommend adding version constraints for stability

### Security Scanning

Suggest improvements for:
- Scanning Docker images for vulnerabilities
- Checking Python dependencies with safety/bandit
- Validating workflow permissions (principle of least privilege)

## 📝 Documentation Requirements

When suggesting workflow changes:

1. **Add inline comments** explaining complex steps
2. **Update README.md** if new workflows affect user workflows
3. **Document new secrets** required for workflows
4. **Include usage examples** for workflow_dispatch inputs
5. **Document workflow improvements** in project documentation

## 🎯 Specific Use Cases

### Adding a New Validation Script

When a new `validate_*.py` script is added:

1. Suggest adding it to the CI workflow for pull request validation
2. Consider if it should be part of the production cycle
3. Check for new dependencies and update requirements.txt
4. Add appropriate test coverage in tests/ directory

### Modifying Docker Configuration

When `Dockerfile` or `.dockerignore` changes:

1. Update docker build steps in production workflow
2. Suggest multi-stage builds for smaller images
3. Check for security best practices (non-root user, minimal base image)
4. Update docker-compose configurations if present

### GPU-Accelerated Computations

When GPU libraries are added (CUDA, PyTorch, JAX):

1. Suggest creating a GPU-specific workflow variant
2. Add CUDA/cuDNN installation steps
3. Configure appropriate runner types
4. Add CPU fallback for compatibility

## ⚙️ Automation Triggers

Copilot should automatically analyze and suggest improvements when:

- New `.py` files are added to the root directory
- `requirements.txt` is modified
- New scripts are added to `scripts/` directory
- Docker or container configuration files change
- Performance issues are identified in workflow runs
- Security vulnerabilities are detected
- Best practices are not followed in existing workflows

## 🔗 Integration with External Systems

### HuggingFace Integration

Monitor for:
- Dataset upload patterns
- Model checkpoint saving
- Results visualization needs

### Docker Registry Integration

Optimize:
- Build caching strategies
- Multi-architecture builds (amd64, arm64)
- Tag management (latest, versioned, commit SHA)

### Cloud Deployment

Suggest workflows for:
- Automated deployment to cloud platforms
- Infrastructure as code updates
- Monitoring and alerting integration

---

**Note**: These instructions are continuously evolving. Copilot should learn from repository patterns and user feedback to provide increasingly relevant suggestions over time.
=======
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
main
