# Enhanced Riemann Hypothesis Validation Workflows

This document describes the enhanced validation workflows implemented for the Riemann-Adelic repository.

## 🔧 Features Implemented

### 1. Enhanced Validation Script (`validate_explicit_formula.py`)
- **CLI Arguments**: Full command-line interface with configurable parameters
- **CSV Output**: Structured results saved to `/data/` directory
- **Logging**: Detailed logs saved to `/logs/` directory
- **Multiple Test Functions**: Support for f1, f2, f3 test functions
- **Error Handling**: Robust error handling and validation

**Usage:**
```bash
python validate_explicit_formula.py \
  --P 1000 \
  --K 50 \
  --test_functions f1 f2 f3 \
  --output_csv data/results.csv
```

### 2. Odlyzko Zeros Management (`utils/fetch_odlyzko.py`)
- **Automatic Download**: Downloads Riemann zeros if not present
- **Validation**: Validates zeros file format (float per line)
- **Error Recovery**: Handles download failures gracefully
- **Multiple Sources**: Tries multiple Odlyzko mirror sources

**Usage:**
```python
from utils.fetch_odlyzko import ensure_zeros_available
ensure_zeros_available()  # Returns True if zeros are available
```

### 3. Comprehensive Test Suite (`tests/test_validation.py`)
- **Mathematical Consistency**: Tests prime_sum, archimedean_sum, zero_sum
- **File Validation**: Tests zeros file validation
- **CSV Output**: Tests result saving functionality
- **Integration Tests**: End-to-end validation tests

**Run tests:**
```bash
python -m pytest tests/ -v
```

### 4. GitHub Actions Workflows

#### A. Enhanced Validation Workflow (`.github/workflows/validate.yml`)
- Runs validation script with configurable parameters
- Downloads zeros data automatically
- Saves results as artifacts
- Supports manual triggers with custom parameters

#### B. Enhanced Notebook Workflow (`.github/workflows/run_notebook.yml`)
- Executes Jupyter notebook with error handling
- Exports HTML to `/docs/` directory
- Handles execution failures gracefully
- Organizes outputs properly

#### C. Comprehensive Validation Pipeline (`.github/workflows/comprehensive_validation.yml`)
- **Complete Pipeline**: Downloads zeros, runs tests, executes validation, processes notebook
- **Scheduled Runs**: Daily validation at 2 AM UTC
- **Parametric Execution**: Configurable validation parameters
- **Result Summarization**: Generates markdown summaries
- **Artifact Management**: Comprehensive artifact collection
- **Error Recovery**: Continues on partial failures

## 📁 Directory Organization

```
├── data/                    # CSV results, summaries
├── logs/                    # Validation logs
├── docs/                    # HTML notebook outputs  
├── zeros/                   # Riemann zeros data
├── notebooks/               # Jupyter notebooks
├── utils/                   # Utility functions
├── tests/                   # Test suite
└── .github/workflows/       # GitHub Actions
```

## 🚀 Usage Examples

### Quick Validation
```bash
# Run with default parameters
python validate_explicit_formula.py

# Run with specific parameters  
python validate_explicit_formula.py --P 1000 --K 50 --test_functions f1 f2
```

### Manual Workflow Trigger
1. Go to GitHub Actions tab
2. Select "Comprehensive RH Validation Pipeline"
3. Click "Run workflow"
4. Configure parameters (optional)
5. View results in artifacts

### Development Testing
```bash
# Run all tests
python -m pytest tests/ -v

# Run demo pipeline
python demo_pipeline.py

# Validate zeros file
python -c "from utils.fetch_odlyzko import validate_zeros_file; print(validate_zeros_file('zeros/zeros_t1e8.txt'))"
```

## 🎯 Workflow Triggers

### Automatic Triggers
- **Push**: Any `.py` file or notebook changes
- **Pull Request**: Validation runs on PRs
- **Schedule**: Daily comprehensive validation

### Manual Triggers
- **workflow_dispatch**: All workflows support manual execution
- **Custom Parameters**: Validation parameters can be configured

## 📊 Output Files

### CSV Results (`data/validation_results_*.csv`)
```csv
timestamp,test_function,prime_sum,archimedean_sum,arithmetic_total,zero_sum,absolute_error,relative_error,P,K,sigma0,T,lim_u
2023-09-14T10:30:00,f1,1.234567,2.345678,3.580245,3.580193,0.000052,1.45e-5,1000,50,2.0,50,5.0
```

### Log Files (`logs/validation_*.log`)
- Detailed execution logs
- Parameter settings
- Function-by-function results
- Error messages and warnings

### Validation Summary (`data/validation_summary.md`)
- Markdown summary of results
- Formatted results table
- Parameter information

## 🔍 Monitoring and Maintenance

### Health Checks
- Zeros file validation on each run
- Test suite execution before validation
- Artifact generation verification

### Error Handling
- Graceful degradation on partial failures
- Retry mechanisms for downloads
- Comprehensive error logging

### Performance
- Configurable parameters for execution time control
- Timeout handling for long computations
- Artifact retention policies (30-90 days)

## 🛠 Troubleshooting

### Common Issues
1. **Zeros file missing**: Automatic download will attempt to resolve
2. **Test failures**: Check mathematical function implementations
3. **Timeout issues**: Reduce P, K parameters for faster execution
4. **Memory issues**: Use smaller parameter values

### Debug Commands
```bash
# Check zeros availability
python -c "from utils.fetch_odlyzko import ensure_zeros_available; ensure_zeros_available()"

# Test individual functions
python -c "from validate_explicit_formula import prime_sum; from utils.mellin import truncated_gaussian; print(prime_sum(truncated_gaussian, 20, 2))"

# Run single test
python -m pytest tests/test_validation.py::test_prime_sum_basic -v
```

This enhanced pipeline provides a robust, automated validation system for the Riemann Hypothesis proof with comprehensive error handling, structured outputs, and flexible configuration options.