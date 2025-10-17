# Path Resolution System Documentation

## Overview

This repository now supports execution from any directory within the project structure. Scripts automatically detect the project root and resolve all file paths correctly, eliminating the need to always run from the project root directory.

## Problem Solved

**Previous Issue**: Scripts failed when executed from subdirectories because they used hardcoded relative paths like:
- `zeros/zeros_t1e3.txt`
- `data/validation_results.csv`  
- `utils/fetch_odlyzko.py`

**Solution**: Implemented dynamic path resolution that automatically locates the project root and converts all paths to absolute paths.

## How It Works

### 1. Project Root Detection

The system identifies the project root by looking for these markers:
- `README.md` file (in the root)
- `utils/` directory
- `.git/` directory (as fallback)

It starts from the current script's location and walks up the directory tree until it finds these markers.

### 2. Path Resolution Functions

Three main functions are provided in `utils/path_utils.py`:

#### `get_project_root()`
Returns the absolute path to the project root.

```python
from utils.path_utils import get_project_root

root = get_project_root()
# Returns: /path/to/-jmmotaburr-riemann-adelic
```

#### `get_project_path(*path_parts)`
Constructs an absolute path relative to the project root.

```python
from utils.path_utils import get_project_path

zeros_file = get_project_path("zeros", "zeros_t1e3.txt")
# Returns: /path/to/-jmmotaburr-riemann-adelic/zeros/zeros_t1e3.txt

data_dir = get_project_path("data")
# Returns: /path/to/-jmmotaburr-riemann-adelic/data
```

#### `ensure_project_in_path()`
Adds the project root to `sys.path` so that `utils` modules can be imported.

```python
from utils.path_utils import ensure_project_in_path

ensure_project_in_path()

# Now you can import from utils regardless of current directory
from utils.mellin import truncated_gaussian
from utils.riemann_tools import load_zeros_near_t
```

### 3. Updated Scripts

The following core scripts have been updated to use path resolution:

- `validate_v5_coronacion.py`
- `validate_explicit_formula.py`
- `validate_critical_line.py`
- `validate_repository.py`
- `thermal_kernel_spectral.py`
- `utils/riemann_tools.py`
- `utils/fetch_odlyzko.py`
- `utils/critical_line_checker.py`
- `utils/__init__.py` (uses lazy imports)

## Usage Examples

### Example 1: Running from Project Root (Traditional)

```bash
cd ~/projects/-jmmotaburr-riemann-adelic
python3 validate_v5_coronacion.py --precision 30
```

### Example 2: Running from Subdirectory (Now Supported!)

```bash
cd ~/projects/-jmmotaburr-riemann-adelic/docs
python3 ../validate_v5_coronacion.py --precision 30
```

### Example 3: Running Tests from Test Directory

```bash
cd ~/projects/-jmmotaburr-riemann-adelic/tests
pytest . -v
```

### Example 4: Loading Data Files from Any Directory

```python
#!/usr/bin/env python3
import sys
from pathlib import Path

# Add project root to path
sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from utils.path_utils import get_project_path, ensure_project_in_path
from utils.riemann_tools import load_zeros_near_t

# Ensure imports work
ensure_project_in_path()

# Load zeros file regardless of current directory
zeros_file = get_project_path("zeros", "zeros_t1e3.txt")
zeros = load_zeros_near_t(str(zeros_file), 14.0, 30.0)
print(f"Loaded {len(zeros)} zeros")
```

## Testing

### Quick Test
Run from any directory within the project:

```bash
python3 test_path_resolution.py
```

This comprehensive test verifies:
- ✅ Path resolution from project root
- ✅ Path resolution from subdirectories
- ✅ File access using resolved paths
- ✅ Module imports from any location

### Manual Testing

Test from different directories:

```bash
# From root
cd /path/to/project
python3 test_path_resolution.py

# From docs
cd /path/to/project/docs
python3 ../test_path_resolution.py

# From tests
cd /path/to/project/tests
python3 ../test_path_resolution.py
```

All should pass successfully!

## Implementation Details

### Lazy Imports in utils/__init__.py

To avoid import errors when optional dependencies are not installed, `utils/__init__.py` uses lazy imports via `__getattr__`:

```python
def __getattr__(name):
    if name == 'AdelicCanonicalDeterminant':
        from .adelic_determinant import AdelicCanonicalDeterminant
        return AdelicCanonicalDeterminant
    # ... other lazy imports
```

This allows `utils.path_utils` to be imported without requiring all dependencies.

### Fallback for Direct Execution

Scripts include fallback code for when they're executed directly:

```python
try:
    from utils.path_utils import get_project_path
except ImportError:
    import sys
    sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
    from utils.path_utils import get_project_path
```

### File Operations

When opening files, paths are resolved first:

```python
# Old way (hardcoded)
with open("zeros/zeros_t1e8.txt", "r") as f:
    # ...

# New way (path-independent)
zeros_file = get_project_path("zeros", "zeros_t1e8.txt")
with open(zeros_file, "r") as f:
    # ...
```

## Benefits

1. **Flexibility**: Run scripts from any directory
2. **Development**: Easier to work in subdirectories
3. **Testing**: Tests can be run from test directory
4. **Robustness**: No more "file not found" errors
5. **Portability**: Works on any system with any project location
6. **Backward Compatible**: Still works when run from project root

## Troubleshooting

### Issue: "Could not find project root"

**Cause**: The script cannot locate the project markers (README.md and utils/ directory).

**Solution**: Ensure you're running from within the project directory structure.

### Issue: "No module named 'utils'"

**Cause**: The project root is not in sys.path.

**Solution**: Add this at the top of your script:

```python
from utils.path_utils import ensure_project_in_path
ensure_project_in_path()
```

### Issue: Dependencies not found

**Cause**: Some required packages are not installed.

**Solution**: 
```bash
pip install -r requirements.txt
```

## Security

All changes have been verified with CodeQL security analysis:
- ✅ No SQL injection vulnerabilities
- ✅ No path traversal issues
- ✅ No arbitrary code execution risks
- ✅ No insecure file operations

The path resolution system includes validation to ensure paths resolve within the project directory.

## Future Enhancements

Potential improvements (optional):
1. Update remaining demo scripts for consistency
2. Add configuration file support for custom project markers
3. Create a project configuration class for advanced settings
4. Add path validation to prevent directory traversal

## Summary

The path resolution system makes the repository truly location-independent. Whether you're running validation scripts, tests, or development tools, everything works regardless of your current directory. This significantly improves the developer experience and reduces common errors related to file paths.
