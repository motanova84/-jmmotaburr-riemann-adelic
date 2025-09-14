# 📚 Validation Workflows Documentation

This document provides comprehensive documentation for the enhanced Riemann Hypothesis validation system with automated workflows, structured output, and error handling.

## 🚀 Quick Start

### Basic Validation
```bash
python validate_explicit_formula.py --P 1000 --max_zeros 2000 --test_functions f1 f2 f3
```

### Download Zeros Data
```bash
python utils/fetch_odlyzko.py --target zeros/zeros_t1e8.txt
```

### Run Tests
```bash
python -m pytest tests/ -v
```

## 🔧 Enhanced Validation Script

### CLI Reference
The `validate_explicit_formula.py` script now supports comprehensive command-line options:

```bash
python validate_explicit_formula.py [OPTIONS]
```

#### Options:
- `--P, --max_primes INT`: Maximum prime P to use (default: 1000, max: 10000)
- `--K INT`: Maximum powers K per prime (default: 5)  
- `--sigma0 FLOAT`: Real part of integration line (default: 2.0)
- `--T INT`: Integration limit T (default: 100)
- `--max_zeros INT`: Maximum number of zeros to use (default: 2000)
- `--test_functions LIST`: Test functions to use (choices: f1, f2, f3, truncated_gaussian)
- `--output_csv PATH`: Output CSV file path (default: data/validation_results.csv)
- `--timeout INT`: Timeout in seconds (default: 300)
- `--lim_u FLOAT`: Integration limit for Mellin transforms (default: 3.0)
- `--log_dir PATH`: Directory for log files (default: logs)

#### Usage Examples:
```bash
# Single function validation
python validate_explicit_formula.py --P 5000 --test_functions f1

# Multiple functions with custom output
python validate_explicit_formula.py --test_functions f1 f2 f3 --output_csv results/my_validation.csv

# High precision validation
python validate_explicit_formula.py --P 10000 --max_zeros 5000 --timeout 900
```

### Test Functions
- **f1**: Truncated Gaussian `exp(-u²/2)` for `|u| ≤ 3`
- **f2**: Alternative Gaussian `exp(-u²)` for `|u| ≤ 2`  
- **f3**: Polynomial `(1 - u²/4)²` for `|u| ≤ 2`
- **truncated_gaussian**: Default from utils.mellin module

## 🗂️ Output Organization

### Directory Structure
```
├── data/          # CSV validation results and summaries
│   ├── validation_results.csv
│   └── comprehensive_results.csv
├── logs/          # Detailed execution logs with timestamps
│   └── validation_YYYYMMDD_HHMMSS.log
├── docs/          # HTML notebook exports and documentation
│   ├── validation_YYYYMMDD_HHMMSS.html
│   └── results_summary.md
└── zeros/         # Riemann zeros data files
    └── zeros_t1e8.txt
```

### CSV Output Format
```csv
parameter,value
f1_arithmetic_side,2.65846663444069
f1_zero_side,-0.00265336477396407
f1_absolute_error,2.66111999921465
f1_relative_error,1.00099808090107
P,50
K,5
sigma0,2.0
T,2
max_zeros,20
timestamp,2025-09-14T17:17:30.514000
```

## 🤖 GitHub Actions Workflows

### 1. Enhanced RH Validation (validate.yml)
**Triggers:**
- Push to `**.py` or `notebooks/**.ipynb`
- Manual dispatch with configurable parameters

**Features:**
- Configurable parameters via workflow dispatch
- Automatic zeros data download
- PyTest execution before validation
- Artifact collection (30-day retention)

**Manual Trigger Parameters:**
- `max_primes`: Maximum number of primes (default: 1000)
- `max_zeros`: Maximum number of zeros (default: 2000) 
- `test_functions`: Space-separated test functions (default: truncated_gaussian)

### 2. Enhanced Notebook Execution (run_notebook.yml)
**Triggers:**
- Push to `notebooks/validation.ipynb`
- Manual dispatch

**Features:**
- Jupyter notebook execution with 300s timeout
- HTML export with timestamp
- Fallback static export on execution failure
- Error reporting and recovery

### 3. Comprehensive Validation Pipeline (comprehensive_validation.yml)
**Triggers:**
- Push to relevant files
- Daily scheduled runs at 2 AM UTC
- Manual dispatch with full parameter control

**Pipeline Stages:**
1. **Setup**: Environment, dependencies, directories
2. **Data Preparation**: Download and validate zeros
3. **Testing**: Run PyTest suite
4. **Validation**: Execute comprehensive validation
5. **Documentation**: Process notebook and generate reports
6. **Artifacts**: Collect all outputs with 90-day retention

**Manual Parameters:**
- `max_primes`: Maximum primes (default: 1000)
- `max_zeros`: Maximum zeros (default: 2000)
- `test_functions`: Test function selection (default: f1 f2 f3)
- `timeout`: Execution timeout (default: 600s)

## 📥 Zeros Data Management

### Automatic Download
The `utils/fetch_odlyzko.py` script provides:

```bash
# Ensure file exists and is valid
python utils/fetch_odlyzko.py --target zeros/zeros_t1e8.txt

# Validate existing file only
python utils/fetch_odlyzko.py --validate_only

# Force re-download
python utils/fetch_odlyzko.py --force_download
```

### Features:
- **Multiple Sources**: Tries multiple mirror URLs for reliability
- **Format Validation**: Validates float-per-line format with error reporting
- **Progress Tracking**: Shows download progress for large files
- **Error Recovery**: Automatic fallback to alternative sources

### Supported Datasets:
- `t1e8`: First 10^8 zeros (default)
- `t1e10`: First 10^10 zeros  
- `t1e12`: First 10^12 zeros

## 🧪 Testing Framework

### Test Suite
Run the comprehensive test suite:
```bash
python -m pytest tests/ -v
```

### Test Coverage:
- **Mathematical Consistency**: Prime sum, archimedean sum, zero sum validation
- **File Operations**: Zeros file availability and format validation
- **CSV Output**: Result saving and logging functionality
- **Integration**: End-to-end validation pipeline tests

## 🚨 Error Handling & Troubleshooting

### Common Issues

**1. Zeros File Not Found**
```
❌ Zeros file not found: zeros/zeros_t1e8.txt
```
**Solution:** Run `python utils/fetch_odlyzko.py --target zeros/zeros_t1e8.txt`

**2. Timeout Errors**
```
❌ Error during computation: timeout
```
**Solution:** Reduce parameters or increase timeout:
```bash
python validate_explicit_formula.py --P 500 --max_zeros 1000 --timeout 600
```

**3. Memory Issues**
**Solution:** Use smaller parameter values:
```bash
python validate_explicit_formula.py --P 1000 --max_zeros 1000 --lim_u 2.0
```

**4. Invalid Zeros Format**
```
❌ Invalid format at line 42: not_a_number
```
**Solution:** Re-download zeros file with `--force_download`

### Performance Optimization

**Recommended Parameter Ranges:**
- **Development/Testing**: P=100-1000, max_zeros=100-1000
- **CI/CD**: P=1000-5000, max_zeros=1000-2000  
- **Research**: P=5000-10000, max_zeros=2000-5000

**Timeout Guidelines:**
- Small validation (P<1000): 60-300s
- Medium validation (P<5000): 300-600s
- Large validation (P≥5000): 600-1200s

## 🔍 Monitoring & Logs

### Log Files
Detailed execution logs are saved to `logs/validation_YYYYMMDD_HHMMSS.log`

**Log Levels:**
- **INFO**: Normal execution progress
- **WARNING**: Non-critical issues (parameter adjustments, format warnings)
- **ERROR**: Critical errors requiring attention

### Health Checks
Workflows include automated health checks:
- ✅ CSV results file creation
- ✅ Log files generation  
- ✅ Zeros data availability
- ✅ Mathematical consistency validation

## 🎯 Validation Results Interpretation

### Success Criteria
- **Absolute Error**: Should be small relative to the values
- **Relative Error**: Typically < 0.01 for good validation
- **Log Output**: No ERROR level messages
- **File Generation**: All expected output files created

### Expected Behavior
The explicit formula validation compares:
- **Arithmetic Side**: Sum over primes + archimedean contribution
- **Spectral Side**: Sum over Riemann zeta zeros

Perfect agreement validates the Riemann Hypothesis for the tested range.

---

**📞 Support:** Check GitHub Issues for common problems and solutions.
**🔄 Updates:** This system supports automated daily validation runs for continuous monitoring.
**⚡ Performance:** All workflows are optimized for GitHub Actions runtime limits with configurable timeouts.