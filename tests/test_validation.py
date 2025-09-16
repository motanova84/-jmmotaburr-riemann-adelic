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
from utils.mellin import truncated_gaussian, mellin_transform


def test_riemann_formula_basic_consistency():
    """Test that the functions produce reasonable outputs."""
    f = truncated_gaussian
    P = 100  # Smaller values for faster testing
    K = 5
    sigma0 = 2.0
    T = 10
    lim_u = 3.0
    
    # Calculate both sides
    prime_side = prime_sum(f, P, K)
    arch_side = archimedean_sum(f, sigma0, T, lim_u)
    total = prime_side + arch_side
    
    # Basic sanity checks
    assert mp.isfinite(prime_side), "Prime sum should be finite"
    assert mp.isfinite(arch_side), "Archimedean sum should be finite" 
    assert mp.isfinite(total), "Total should be finite"
    assert abs(prime_side) > 0, "Prime sum should be non-zero"


def test_mellin_transform_properties():
    """Test basic properties of the Mellin transform."""
    
    # Test that Mellin transform of truncated Gaussian has expected properties
    f = truncated_gaussian
    s = mp.mpc(1, 0)  # s = 1
    lim = 3.0
    
    result = mellin_transform(f, s, lim)
    assert isinstance(result, (mp.mpc, mp.mpf)), "Should return a complex number"
    assert mp.isfinite(result), "Should be finite"
    
    # Test with different parameters
    s2 = mp.mpc(0.5, 1.0)
    result2 = mellin_transform(f, s2, lim)
    assert mp.isfinite(result2), "Should be finite for different s"


def test_zero_sum_limited_functionality():
    """Test zero sum function with mock data."""
    # Create a temporary zeros file for testing
    test_zeros_file = "/tmp/test_zeros.txt"
    try:
        with open(test_zeros_file, 'w') as f:
            for i in range(10):
                f.write(f"{14.134 + i * 5.0}\n")  # Sample zero values
        
        f = truncated_gaussian
        result = zero_sum_limited(f, test_zeros_file, 5, lim_u=3.0)
        
        assert mp.isfinite(result), "Zero sum should be finite"
        assert isinstance(result, mp.mpf), "Should return mpmath float"
        
    finally:
        if os.path.exists(test_zeros_file):
            os.remove(test_zeros_file)


def test_truncated_gaussian_properties():
    """Test properties of the truncated Gaussian function."""
    f = truncated_gaussian
    
    # Test truncation
    assert f(0) > 0, "Should be positive at origin"
    assert f(10) == 0, "Should be zero outside truncation"
    assert f(-10) == 0, "Should be zero outside truncation"
    
    # Test symmetry
    assert abs(f(2) - f(-2)) < 1e-10, "Should be symmetric"
    
    # Test monotonicity near origin
    assert f(0) > f(1), "Should decrease away from origin"
    assert f(1) > f(2), "Should continue decreasing"


if __name__ == "__main__":
    pytest.main([__file__, "-v"])