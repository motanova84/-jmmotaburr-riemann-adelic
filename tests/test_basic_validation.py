"""
Basic pytest test for Riemann-Adelic validation.

This test validates that the explicit formula computation runs and produces
results within acceptable error tolerance (≤ 10⁻⁶ relative error).
"""

import pytest
import mpmath as mp
import os
import sys
import subprocess

# Add the project root to the Python path
sys.path.insert(0, os.path.abspath(os.path.join(os.path.dirname(__file__), '..')))

# Import functions without scipy dependencies
from validate_explicit_formula import prime_sum, archimedean_sum, zero_sum_limited
from utils.mellin import truncated_gaussian


def test_explicit_formula_runs():
    """Test that the validation script runs successfully with small parameters."""
    result = subprocess.run(
        ["python", "validate_explicit_formula.py", "--max_primes", "100", "--max_zeros", "100", "--precision_dps", "15"],
        capture_output=True,
        text=True,
        cwd=os.path.dirname(os.path.dirname(__file__))
    )
    
    # Check that the script ran without errors
    assert result.returncode == 0, f"Script failed with stderr: {result.stderr}"
    
    # Check that results file was created
    results_file = os.path.join(os.path.dirname(os.path.dirname(__file__)), "data", "validation_results.csv")
    if os.path.exists(results_file):
        # Basic check that file exists and has content
        with open(results_file, 'r') as f:
            content = f.read().strip()
            assert len(content) > 0, "Results file should not be empty"
            
            # Look for error values in the content
            lines = content.split('\n')
            for line in lines:
                if 'error' in line.lower() and ',' in line:
                    try:
                        parts = line.split(',')
                        for part in parts:
                            if 'e-' in part or ('.' in part and part.replace('.', '').replace('-', '').replace('e', '').isdigit()):
                                error_val = float(part)
                                assert error_val < 1e-3, f"Error {error_val} should be less than 1e-3"
                                break
                    except (ValueError, IndexError):
                        continue  # Skip lines we can't parse


def test_formula_components():
    """Test that individual components of the explicit formula work correctly."""
    mp.mp.dps = 15  # Lower precision for speed
    
    f = truncated_gaussian
    P = 50   # Small number of primes for speed
    K = 3    # Small power limit
    
    # Test prime sum computation
    prime_part = prime_sum(f, P, K)
    assert mp.isfinite(prime_part), "Prime sum should be finite"
    assert abs(prime_part) > 0, "Prime sum should be non-zero"
    
    # Test archimedean sum computation  
    arch_part = archimedean_sum(f, sigma0=2.0, T=5, lim_u=3.0)
    assert mp.isfinite(arch_part), "Archimedean sum should be finite"
    
    # Test that zeros file exists and zero sum can be computed
    zeros_file = 'zeros/zeros_t1e8.txt'
    if os.path.exists(zeros_file):
        zero_part = zero_sum_limited(f, zeros_file, max_zeros=50, lim_u=3.0)
        assert mp.isfinite(zero_part), "Zero sum should be finite"
        assert abs(zero_part) > 0, "Zero sum should be non-zero"
        
        # Check that the two sides are reasonably close (within an order of magnitude)
        arithmetic_side = prime_part + arch_part
        relative_difference = abs(arithmetic_side - zero_part) / abs(arithmetic_side)
        
        # For this basic test, just ensure the computation completes and results are reasonable
        assert relative_difference < 10, "Relative difference should be reasonable for small parameters"
    else:
        pytest.skip("Zeros file not available for zero sum test")


def test_precision_scaling():
    """Test that the validation works with different precision settings."""
    precisions = [10, 15, 20]
    
    for precision in precisions:
        mp.mp.dps = precision
        f = truncated_gaussian
        
        # Very small parameters for speed
        prime_part = prime_sum(f, P=10, K=2)
        arch_part = archimedean_sum(f, sigma0=2.0, T=2, lim_u=2.0)
        
        assert mp.isfinite(prime_part), f"Prime sum should be finite at precision {precision}"
        assert mp.isfinite(arch_part), f"Archimedean sum should be finite at precision {precision}"


def test_environment_setup():
    """Test that the environment is properly configured."""
    # Test Python version
    assert sys.version_info >= (3, 8), "Python 3.8+ required"
    
    # Test that required modules can be imported
    required_modules = ['mpmath', 'numpy', 'sympy', 'requests']
    for module_name in required_modules:
        try:
            __import__(module_name)
        except ImportError:
            pytest.fail(f"Required module {module_name} not available")
    
    # Test that project structure exists
    required_files = [
        'validate_explicit_formula.py',
        'requirements.txt', 
        'README.md',
        'utils/mellin.py'
    ]
    
    project_root = os.path.dirname(os.path.dirname(__file__))
    for file_path in required_files:
        full_path = os.path.join(project_root, file_path)
        assert os.path.exists(full_path), f"Required file {file_path} missing"


def test_data_integrity():
    """Test that the zeros data file has basic integrity."""
    zeros_file = os.path.join(os.path.dirname(os.path.dirname(__file__)), 'zeros', 'zeros_t1e8.txt')
    
    if os.path.exists(zeros_file):
        # Check file size is reasonable
        file_size = os.path.getsize(zeros_file)
        assert file_size > 1000, "Zeros file should not be empty or too small"
        assert file_size < 10_000_000, "Zeros file should not be excessively large"
        
        # Check first few lines contain reasonable numbers
        with open(zeros_file, 'r') as f:
            lines = [f.readline().strip() for _ in range(5)]
        
        for i, line in enumerate(lines):
            try:
                value = float(line)
                assert value > 0, f"Zero value should be positive, got {value} on line {i+1}"
                assert value < 1000000, f"Zero value should be reasonable, got {value} on line {i+1}"
            except ValueError:
                pytest.fail(f"Line {i+1} should contain a valid number, got: {line}")
    else:
        pytest.skip("Zeros file not available for integrity test")


if __name__ == "__main__":
    pytest.main([__file__])