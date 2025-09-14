# Riemann-Adelic

This repository contains numerical validation code for the paper:

**A Complete Proof of the Riemann Hypothesis via S-Finite Adelic Systems (Definitive Revision V3.6)**  
Author: José Manuel Mota Burruezo  
Date: September 13, 2025  
DOI: [[coming soon]  ](https://zenodo.org/uploads/17114751)
Notebook Validation Commit: `abc123`

## 🧪 Objective

Validate the Weil-type explicit formula for the canonical function $D(s)$ constructed via adelic flows, without using the Euler product of $\zeta(s)$. The validation includes:

- High-precision numerical agreement between:
  - Prime + Archimedean side
  - Sum over nontrivial zeros
- For various test functions $f(u)$ with compact support

## 📂 Structure

```plaintext
.
├── notebooks/                  # Jupyter notebooks (e.g. validation.ipynb)
├── utils/
│   └── mellin.py              # Tools for computing Mellin transforms
├── zeros/
│   └── zeros_t1e8.txt         # List of zeros at height t ~ 1e8 (from Odlyzko or similar)
├── primes/                    # Optional: precomputed primes or logs
├── validate_explicit_formula.py  # Main CLI validation script
├── requirements.txt
└── README.md
```

## 🤖 Automated Workflows

This repository includes comprehensive GitHub Actions workflows for automated validation and testing:

### 📋 Available Workflows

#### 1. **Validation Workflow** (`validate.yml`)
Runs on every push and provides comprehensive validation of the Riemann explicit formula.

**Features:**
- Multi-stage validation with different parameter sets
- Automatic Odlyzko zeros data fetching and validation
- CSV result output organized in `/data/` directory
- Structured logging in `/logs/` directory
- Artifact upload with 30-day retention
- Matrix testing across Python versions

**Manual Trigger:** 
```bash
# Via GitHub UI or CLI
gh workflow run validate.yml -f test_functions="f1 f2 f3" -f max_primes=2000
```

#### 2. **Notebook Execution** (`run_notebook.yml`)  
Executes Jupyter notebooks and exports HTML with comprehensive error handling.

**Features:**
- Automatic notebook execution with timeout controls
- HTML export to `docs/` directory
- Execution status reporting and error analysis
- GitHub Pages deployment on main branch
- PR comments with execution results

#### 3. **Comprehensive CI Pipeline** (`comprehensive.yml`)
Advanced workflow with intelligent change detection and multi-matrix testing.

**Features:**
- Smart change detection (only runs relevant jobs)
- Multi-parameter validation matrices
- Lint and code quality checks
- Integration tests with data integrity verification
- Comprehensive reporting and artifact management

#### 4. **Odlyzko Data Management** (`odlyzko_data.yml`)
Specialized workflow for managing Riemann zeros data.

**Features:**
- On-demand data fetching with validation
- Multiple dataset support (t1e8, t1e10, t1e12) 
- Data integrity verification
- Weekly automated data checks
- Caching and artifact management

### 🔧 Manual Execution

#### Run Validation Locally
```bash
# Basic validation with default parameters
python validate_explicit_formula.py

# Custom validation
python validate_explicit_formula.py \
  --max_primes 500 \
  --test_functions f1 f2 \
  --delta 0.01 \
  --output data/my_validation.csv

# Help for all options
python validate_explicit_formula.py --help
```

#### Data Management
```bash
# Fetch and validate Odlyzko zeros
python utils/fetch_odlyzko.py --dataset t1e8

# List available datasets
python utils/fetch_odlyzko.py --list

# Force re-download
python utils/fetch_odlyzko.py --dataset t1e8 --force
```

#### Result Analysis
```bash
# Organize validation results
python utils/riemann_tools.py --organize

# Generate summary report  
python utils/riemann_tools.py --report

# Check data integrity
python utils/riemann_tools.py --check-integrity

# Clean old logs (keep 7 days)
python utils/riemann_tools.py --clean-logs 7
```

### 📊 Output Organization

The workflows automatically organize outputs into a structured hierarchy:

```
📁 Project Structure
├── data/                    # Validation results and analysis
│   ├── validation_*.csv     # Timestamped validation results  
│   ├── results/            # Organized results by date
│   ├── archives/           # Archived historical results
│   └── summary_report_*.md # Generated analysis reports
├── logs/                   # Execution logs
│   └── validation_*.log    # Timestamped execution logs
├── docs/                   # Generated documentation
│   ├── validation.html     # Executed notebook output
│   └── execution_*.html    # Execution reports
└── zeros/                  # Riemann zeros data
    ├── zeros_t1e8.txt     # Cached zeros data
    └── *.gz               # Compressed downloads (auto-cleaned)
```

### 🎯 Workflow Triggers

| Workflow | Automatic Triggers | Manual Triggers |
|----------|-------------------|-----------------|
| Validation | Push to `.py` files, PRs | Workflow dispatch with parameters |
| Notebook | Push to `validation.ipynb` | Workflow dispatch |
| Comprehensive | Push to main, PRs | Workflow dispatch with options |
| Data Management | Weekly schedule | Workflow dispatch with dataset choice |

### 🔄 Integration with Development

#### For Contributors
1. **Push changes** → Automatic validation runs
2. **Open PR** → CI runs full test suite with reporting  
3. **Merge to main** → Results deployed to GitHub Pages

#### For Research
1. **Workflow dispatch** → Run validation with specific parameters
2. **Download artifacts** → Access CSV results and logs
3. **View reports** → Analyze validation trends and performance

### ⚙️ Configuration

Key parameters can be customized via workflow inputs:

- `test_functions`: Which test functions to validate (f1, f2, f3)
- `max_primes`: Maximum prime number for validation
- `delta`: Validation tolerance threshold
- `dataset`: Odlyzko zeros dataset to use
- `run_validation`: Force full validation run
- `run_notebook`: Force notebook execution

### 🔍 Monitoring and Debugging

- **Real-time logs**: Available during workflow execution
- **Artifact downloads**: Access results, logs, and reports
- **PR comments**: Automatic status updates on pull requests
- **GitHub Pages**: Published results and analysis
- **Data integrity**: Automated verification and reporting

## 🤖 Quick Copilot Integration

The comprehensive workflow system has been implemented with the following capabilities:

✅ **Automated validation** via `validate_explicit_formula.py` with logging and CSV output  
✅ **Jupyter notebook execution** with HTML export and error handling  
✅ **Odlyzko zeros downloading** with validation and integrity checks  
✅ **Pytest testing** for mathematical consistency and integration tests  
✅ **Output organization** into `/data/` and `/logs/` with structured archiving

### 🚀 Quick Start Commands

```bash
# Run validation with recommended parameters
python validate_explicit_formula.py --max_primes 1000 --max_powers 50 --T 50 --test_functions f1 f2

# Execute and export notebook  
jupyter nbconvert --to html --execute notebooks/validation.ipynb --output-dir docs/

# Fetch zeros data
python utils/fetch_odlyzko.py --dataset t1e8

# Run tests
pytest tests/ -v

# Organize results
python utils/riemann_tools.py --organize --report
```

All workflows support the specified reproducible parameters: `δ = 0.01`, `P = 1000`, `K = 50`, `σ₀ = 2`, `T = 50`.
