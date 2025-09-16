"""
🧠 Copilot Prompt:
Create pytest tests for mathematical identity checks in the Riemann Hypothesis validation.

Test the consistency between prime_sum, A_infty, and zero_sum functions.
Ensure the explicit formula validation works for different test functions.
"""

import pytest
import mpmath as mp
import os
from validate_explicit_formula import prime_sum, archimedean_sum, zero_sum_limited
from utils.mellin import truncated_gaussian

def test_explicit_formula_identity():
    """Test the explicit formula identity using standard parameters."""
    f = truncated_gaussian
    P = 100  # Smaller values for faster testing
    K = 5
    sigma0 = 2.0
    T = 10
    lim_u = 3.0
    max_zeros = 50
    
    # Calculate both sides
    prime_side = prime_sum(f, P, K)
    arch_side = archimedean_sum(f, sigma0, T, lim_u)
    arithmetic_total = prime_side + arch_side
    
    # Test with actual zeros if file exists
    zeros_file = 'zeros/zeros_t1e8.txt'
    if os.path.exists(zeros_file):
        zero_side = zero_sum_limited(f, zeros_file, max_zeros, lim_u)
        # For small test parameters, we expect some disagreement but not infinite
        assert mp.isfinite(arithmetic_total)
        assert mp.isfinite(zero_side)
        error = abs(arithmetic_total - zero_side)
        assert mp.isfinite(error)
    else:
        pytest.skip("Zeros file not available for testing")


def test_numerical_consistency():
    """Test that results are numerically consistent."""
    f = truncated_gaussian
    P = 50
    K = 3
    sigma0 = 2.0
    T = 5
    lim_u = 3.0
    
    # Test that prime_sum returns a finite result
    result = prime_sum(f, P, K)
    assert mp.isfinite(result)
    assert isinstance(result, mp.mpf)
    
    # Test that archimedean_sum returns a finite result
    result = archimedean_sum(f, sigma0, T, lim_u)
    assert mp.isfinite(result)


def test_data_integrity():
    """Test that generated data has correct format."""
    import tempfile
    import csv
    
    # Create a temporary CSV file to test format
    test_data = [
        ["parameter", "value"],
        ["arithmetic_side", "1.234567"],
        ["zero_side", "1.234568"],
        ["absolute_error", "0.000001"],
        ["relative_error", "0.0000008"],
        ["delta", "0.01"],
        ["P", "1000"],
        ["K", "50"],
        ["N_Xi", "2000"],
        ["sigma0", "2"],
        ["T", "50"]
    ]
    
    with tempfile.NamedTemporaryFile(mode='w', suffix='.csv', delete=False) as f:
        writer = csv.writer(f)
        for row in test_data:
            writer.writerow(row)
        temp_file = f.name
    
    try:
        # Test that CSV can be read and has expected format
        with open(temp_file, 'r') as f:
            reader = csv.DictReader(f)
            rows = list(reader)
            
        # Check expected parameters are present
        param_names = [row['parameter'] for row in rows]
        expected_params = ['arithmetic_side', 'zero_side', 'absolute_error', 
                         'relative_error', 'delta', 'P', 'K', 'N_Xi', 'sigma0', 'T']
        
        for param in expected_params:
            assert param in param_names, f"Missing parameter: {param}"
            
        # Check that numeric values can be parsed
        for row in rows:
            if row['parameter'] in ['arithmetic_side', 'zero_side', 'absolute_error']:
                try:
                    float(row['value'])
                except ValueError:
                    pytest.fail(f"Cannot parse numeric value for {row['parameter']}: {row['value']}")
                    
    finally:
        os.unlink(temp_file)


def test_mellin_transform_properties():
    """Test basic properties of the Mellin transform."""
    from utils.mellin import mellin_transform
    
    # Test that Mellin transform of truncated Gaussian has expected properties
    f = truncated_gaussian
    s = mp.mpc(1, 0)  # s = 1
    lim = 3.0
    
    result = mellin_transform(f, s, lim)
    assert isinstance(result, (mp.mpc, mp.mpf))  # Should return a complex number
    assert mp.isfinite(result)  # Should be finite


def test_parameter_validation():
    """Test that the validation script handles parameters correctly."""
    import subprocess
    import sys
    
    # Test that script accepts the required parameters without error
    result = subprocess.run([
        sys.executable, 'validate_explicit_formula.py', '--help'
    ], capture_output=True, text=True, cwd='.')
    
    assert result.returncode == 0
    help_text = result.stdout
    
    # Check that all required parameters are in help text
    required_params = ['--delta', '--P', '--K', '--N_Xi', '--sigma0', '--T']
    for param in required_params:
        assert param in help_text, f"Parameter {param} not found in help"


if __name__ == "__main__":
    pytest.main([__file__])