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
