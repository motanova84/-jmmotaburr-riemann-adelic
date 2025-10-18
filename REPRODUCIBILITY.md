# CI/CD Reproducibility Guide

This document describes the reproducibility measures implemented in this repository's CI/CD pipelines.

## Overview

To ensure reproducible builds and consistent results across different environments and time periods, this repository implements several key practices:

1. **Pinned Dependencies** - Exact version specifications for all dependencies
2. **Standardized Python Version** - Consistent Python version across all workflows
3. **Pinned Build Tools** - Fixed versions of pip and other build tools
4. **Reproducible Data** - Checksums and versioning for computational data

## Dependency Management

### Requirements Files

This repository maintains two requirements files:

- **`requirements.txt`**: Base requirements with version ranges for development flexibility
- **`requirements-lock.txt`**: Pinned versions for CI/CD reproducibility

### Using Requirements-Lock

All CI/CD workflows use `requirements-lock.txt` to ensure reproducible builds:

```bash
python -m pip install --upgrade pip==24.3.1
pip install -r requirements-lock.txt
```

### Updating Dependencies

To update dependencies while maintaining reproducibility:

1. Update `requirements.txt` with new version constraints
2. Create a clean virtual environment:
   ```bash
   python3.11 -m venv venv
   source venv/bin/activate
   ```
3. Install and freeze dependencies:
   ```bash
   pip install --upgrade pip==24.3.1
   pip install -r requirements.txt
   pip freeze > requirements-lock.txt
   ```
4. Manually clean `requirements-lock.txt` to remove system packages
5. Test the changes locally and in CI before merging

## Python Version Standardization

All workflows use **Python 3.11** for consistency:

```yaml
- name: Set up Python
  uses: actions/setup-python@v5
  with:
    python-version: '3.11'
```

### Why Python 3.11?

- Widely adopted across the project's existing workflows
- Stable and well-supported
- Compatible with all project dependencies
- Balance between new features and stability

## Build Tool Pinning

### Pip Version

All workflows pin pip to version **24.3.1**:

```bash
python -m pip install --upgrade pip==24.3.1
```

This ensures consistent behavior of package installation across runs.

## Dependency Caching

To speed up builds while maintaining reproducibility, this repository uses dependency caching in CI workflows. There are two main approaches:

1. **Built-in pip cache via `setup-python`** (predominant pattern):

   ```yaml
   - name: Set up Python
     uses: actions/setup-python@v5
     with:
       python-version: '3.11'
       cache: 'pip'
The cache key includes:
- Operating system
- Python version
- Hash of requirements-lock.txt

This ensures the cache is invalidated when dependencies change.

## Computational Data Reproducibility

### Riemann Zeros Data

The project uses pre-computed Riemann zeta zeros from Odlyzko's tables:

- Data is fetched from canonical sources
- Checksums validate data integrity
- Version tags (t1e8, t1e10, etc.) ensure consistent datasets

### Validation Parameters

CI workflows use consistent parameters for reproducibility:

```yaml
env:
  PRIME_COUNT: 100
  ZERO_COUNT: 100
  PRIME_POWERS: 3
  INTEGRATION_T: 10
  PRECISION_DPS: 15
```

These are documented in each workflow file and can be overridden for manual runs.

## Workflow Consistency

### Common Patterns

All workflows follow these patterns:

1. **Checkout**: `actions/checkout@v4`
2. **Python Setup**: `actions/setup-python@v5` with version 3.11
3. **Dependency Installation**: Using requirements-lock.txt with pinned pip
4. **Caching**: Using requirements-lock.txt hash in cache keys

### Workflow Types

- **Quick CI** (`quick.yml`): Fast validation on every push
- **Comprehensive CI** (`comprehensive-ci.yml`): Full validation suite
- **Full Validation** (`full.yml`): Manual high-precision runs
- **Specialized Workflows**: Latex, proof checks, etc.

## Artifacts and Retention

Results are stored as artifacts with appropriate retention periods:

- Test results: 30 days
- Validation reports: 30 days
- Consolidated reports: 90 days

## Verification

To verify reproducibility:

1. Run the same workflow multiple times
2. Compare output artifacts
3. Verify checksums match
4. Ensure numerical results are within expected precision bounds

## Troubleshooting

### Cache Issues

If cache causes problems:
```bash
# Clear cache manually in GitHub Actions UI
# Or increment cache version in workflow
key: v2-${{ runner.os }}-python-3.11-${{ hashFiles('**/requirements-lock.txt') }}
```

### Dependency Conflicts

If dependencies conflict:
1. Check requirements-lock.txt for version mismatches
2. Recreate the lock file from scratch
3. Test in a clean environment

### Numerical Precision

Mathematical computations may vary slightly due to:
- Floating-point arithmetic differences
- Library implementation changes
- Hardware variations

Expected tolerance levels are documented in test assertions.

## Best Practices

1. **Always use requirements-lock.txt in CI/CD**
2. **Test dependency updates thoroughly**
3. **Document any manual interventions**
4. **Keep lock files up to date with security patches**
5. **Review changes in lock files during code review**

## References

- [pip documentation](https://pip.pypa.io/)
- [GitHub Actions caching](https://docs.github.com/en/actions/using-workflows/caching-dependencies-to-speed-up-workflows)
- [Python version support](https://devguide.python.org/versions/)

## Version History

- **2025-10-18**: Initial implementation
  - Created requirements-lock.txt
  - Standardized Python 3.11 across all workflows
  - Pinned pip to version 24.3.1
  - Updated all workflow caching strategies
